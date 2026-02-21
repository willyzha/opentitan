// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, Result};
use cryptoki::mechanism::vendor_defined::VendorDefinedMechanism;
use cryptoki::mechanism::Mechanism;
use cryptoki::object::Attribute;
use cryptoki::session::Session;
use der::{DecodePem, Encode, EncodePem};
use rand::Rng;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::any::Any;
use std::fs;
use std::path::PathBuf;
use std::time::{Duration, SystemTime};
use x509_cert::certificate::{Certificate, TbsCertificate, Version};
use x509_cert::ext::pkix::{
    AuthorityKeyIdentifier, BasicConstraints, KeyUsage, SubjectKeyIdentifier,
};
use x509_cert::ext::Extension;
use x509_cert::serial_number::SerialNumber;
use x509_cert::spki::AlgorithmIdentifierOwned;
use x509_cert::time::{Time, Validity};
use spki::AssociatedAlgorithmIdentifier;

use crate::commands::{BasicResult, Dispatch};
use crate::error::HsmError;
use crate::module::Module;
use crate::util::attribute::{AttributeMap, AttributeType, KeyType, MechanismType, ObjectClass};
use crate::util::helper;

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct EndorseCert {
    /// Unique identifier of the private key to use for signing.
    #[arg(long)]
    id: Option<String>,
    /// Label of the private key to use for signing.
    #[arg(short, long)]
    label: Option<String>,
    /// Path to the CSR to be endorsed.
    #[arg(long)]
    csr: PathBuf,
    /// Path to the CA certificate. If omitted, generates a self-signed root certificate.
    #[arg(long)]
    ca_cert: Option<PathBuf>,
    /// Path to the file where the certificate will be saved.
    #[arg(short, long)]
    output: PathBuf,
    /// Number of days the certificate is valid for. Use -1 for no expiry.
    #[arg(long, default_value = "7300")]
    days: i64,
}

impl EndorseCert {
    fn run_command(&self, session: &Session) -> Result<()> {
        // Find the private key
        let mut attrs = helper::search_spec(self.id.as_deref(), self.label.as_deref())?;
        attrs.push(Attribute::Class(ObjectClass::PrivateKey.try_into()?));
        attrs.push(Attribute::KeyType(KeyType::MlDsa.try_into()?));
        let private_key = helper::find_one_object(session, &attrs)?;

        // Get CA private key OID using ParameterSet
        let map = AttributeMap::from_object(session, private_key)?;
        let parameter_set = map
            .get(&AttributeType::ParameterSet)
            .and_then(|d| u64::try_from(d).ok())
            .ok_or(anyhow::anyhow!("missing parameter_set"))?;
        let oid = match parameter_set {
            1 => ml_dsa::MlDsa44::ALGORITHM_IDENTIFIER.oid,
            2 => ml_dsa::MlDsa65::ALGORITHM_IDENTIFIER.oid,
            3 => ml_dsa::MlDsa87::ALGORITHM_IDENTIFIER.oid,
            _ => return Err(anyhow::anyhow!("unsupported parameter_set")),
        };

        let algorithm = AlgorithmIdentifierOwned {
            oid,
            parameters: None,
        };

        let csr_pem = fs::read(&self.csr)?;
        let csr = x509_cert::request::CertReq::from_pem(&csr_pem)
            .map_err(|e| anyhow!("Failed to parse CSR: {}", e))?;

        let (issuer, aki_bytes) = if let Some(ca_cert_path) = &self.ca_cert {
            let ca_cert_pem = fs::read(ca_cert_path)?;
            let ca_cert = Certificate::from_pem(&ca_cert_pem)
                .map_err(|e| anyhow!("Failed to parse CA Certificate: {}", e))?;

            let issuer = ca_cert.tbs_certificate.subject.clone();

            let ca_pub_key_bytes = ca_cert
                .tbs_certificate
                .subject_public_key_info
                .subject_public_key
                .as_bytes()
                .ok_or(anyhow!("Invalid CA public key bytes"))?;

            let mut hasher_ca = Sha256::new();
            hasher_ca.update(ca_pub_key_bytes);
            let aki = hasher_ca.finalize()[0..20].to_vec();
            (issuer, Some(aki))
        } else {
            // Self-signed root CA
            (csr.info.subject.clone(), None)
        };

        let subject = csr.info.subject.clone();
        let subject_public_key_info = csr.info.public_key.clone();

        let sub_pub_key_bytes = subject_public_key_info
            .subject_public_key
            .as_bytes()
            .ok_or(anyhow!("Invalid subject public key bytes"))?
            .to_vec();

        // Validity
        let now = SystemTime::now();
        let not_before = Time::try_from(now).map_err(|e| anyhow!("Time error: {}", e))?;

        let not_after = if self.days == -1 {
            // RFC 5280 4.1.2.5: To indicate that a certificate has no well-defined
            // expiration date, the notAfter SHOULD be assigned the GeneralizedTime
            // value of 99991231235959Z.
            let no_expiry = der::asn1::GeneralizedTime::from_date_time(
                der::DateTime::new(9999, 12, 31, 23, 59, 59)
                    .map_err(|e| anyhow!("DateTime error: {}", e))?,
            );
            Time::GeneralTime(no_expiry)
        } else {
            let days_u64 = u64::try_from(self.days)
                .map_err(|_| anyhow!("Invalid number of days: {}", self.days))?;
            let not_after_time = now + Duration::from_secs(days_u64 * 24 * 60 * 60);
            Time::try_from(not_after_time).map_err(|e| anyhow!("Time error: {}", e))?
        };

        let validity = Validity {
            not_before,
            not_after,
        };

        // Serial Number
        let mut serial_bytes = [0u8; 16];
        rand::thread_rng().fill(&mut serial_bytes);
        let serial_number = SerialNumber::new(&serial_bytes)
            .map_err(|e| anyhow!("Invalid serial number: {}", e))?;

        // Extensions
        let mut extensions = Vec::new();

        // Basic Constraints
        let basic_constraints = BasicConstraints {
            ca: true,
            path_len_constraint: None,
        };
        extensions.push(Extension {
            extn_id: const_oid::db::rfc5280::ID_CE_BASIC_CONSTRAINTS,
            critical: true,
            extn_value: x509_cert::der::asn1::OctetString::new(basic_constraints.to_der()?)?,
        });

        // Key Usage
        let key_usage = KeyUsage::from(
            x509_cert::ext::pkix::KeyUsages::DigitalSignature
                | x509_cert::ext::pkix::KeyUsages::KeyCertSign
                | x509_cert::ext::pkix::KeyUsages::CRLSign,
        );
        extensions.push(Extension {
            extn_id: const_oid::db::rfc5280::ID_CE_KEY_USAGE,
            critical: true,
            extn_value: x509_cert::der::asn1::OctetString::new(key_usage.to_der()?)?,
        });

        // Subject Key Identifier
        let mut hasher = Sha256::new();
        hasher.update(&sub_pub_key_bytes);
        let ski_bytes = &hasher.finalize()[0..20];
        let ski = SubjectKeyIdentifier(x509_cert::der::asn1::OctetString::new(ski_bytes)?);
        extensions.push(Extension {
            extn_id: const_oid::db::rfc5280::ID_CE_SUBJECT_KEY_IDENTIFIER,
            critical: false,
            extn_value: x509_cert::der::asn1::OctetString::new(ski.to_der()?)?,
        });

        // Authority Key Identifier (if endorsing)
        if let Some(aki_bytes) = aki_bytes {
            let aki = AuthorityKeyIdentifier {
                key_identifier: Some(x509_cert::der::asn1::OctetString::new(
                    aki_bytes.as_slice(),
                )?),
                authority_cert_issuer: None,
                authority_cert_serial_number: None,
            };
            extensions.push(Extension {
                extn_id: const_oid::db::rfc5280::ID_CE_AUTHORITY_KEY_IDENTIFIER,
                critical: false,
                extn_value: x509_cert::der::asn1::OctetString::new(aki.to_der()?)?,
            });
        }

        let tbs_cert = TbsCertificate {
            version: Version::V3,
            serial_number,
            signature: algorithm.clone(),
            issuer,
            validity,
            subject,
            subject_public_key_info,
            issuer_unique_id: None,
            subject_unique_id: None,
            extensions: Some(extensions),
        };

        // Serialize TBS to sign
        let tbs_bytes = tbs_cert
            .to_der()
            .map_err(|e| anyhow!("Failed to encode TbsCertificate: {}", e))?;

        // Sign using HSM
        let mechanism = Mechanism::VendorDefined(VendorDefinedMechanism::new::<()>(
            MechanismType::MlDsa.try_into()?,
            None,
        ));

        let signature_bytes = session
            .sign(&mechanism, private_key, &tbs_bytes)
            .map_err(|e| anyhow!("HSM signing failed: {}", e))?;

        let signature = x509_cert::der::asn1::BitString::from_bytes(&signature_bytes)
            .map_err(|e| anyhow!("Invalid signature bytes: {}", e))?;

        let cert = Certificate {
            tbs_certificate: tbs_cert,
            signature_algorithm: algorithm,
            signature,
        };

        // Encode to PEM
        let pem = cert
            .to_pem(Default::default())
            .map_err(|e| anyhow!("Failed to encode Certificate to PEM: {}", e))?;
        fs::write(&self.output, pem.as_bytes())?;

        Ok(())
    }
}

#[typetag::serde(name = "mldsa-endorse-cert")]
impl Dispatch for EndorseCert {
    fn run(
        &self,
        _context: &dyn Any,
        _hsm: &Module,
        session: Option<&Session>,
    ) -> Result<Box<dyn erased_serde::Serialize>> {
        let session = session.ok_or(HsmError::SessionRequired)?;
        self.run_command(session)?;
        Ok(Box::<BasicResult>::default())
    }
}
