use aws_lc_rs::aead::{self, LessSafeKey, UnboundKey};
use noise_protocol::Cipher;

use crate::sensitive::Sensitive;

const TAGLEN: usize = 16;

pub enum ChaCha20Poly1305 {}

impl Cipher for ChaCha20Poly1305 {
    fn name() -> &'static str {
        "ChaChaPoly"
    }

    type Key = Sensitive<[u8; 32]>;

    fn encrypt(k: &Self::Key, nonce: u64, ad: &[u8], plaintext: &[u8], out: &mut [u8]) {
        assert!(plaintext.len().checked_add(TAGLEN) == Some(out.len()));

        let mut nonce_bytes = [0u8; 12];
        nonce_bytes[4..].copy_from_slice(&nonce.to_le_bytes());
        let nonce = aead::Nonce::assume_unique_for_key(nonce_bytes);

        let key =
            LessSafeKey::new(UnboundKey::new(&aead::CHACHA20_POLY1305, k.as_slice()).unwrap());

        let (in_out, tag_out) = out.split_at_mut(plaintext.len());
        in_out.copy_from_slice(plaintext);

        let tag = key
            .seal_in_place_separate_tag(nonce, aead::Aad::from(ad), in_out)
            .unwrap();
        tag_out.copy_from_slice(tag.as_ref());
    }

    fn encrypt_in_place(
        k: &Self::Key,
        nonce: u64,
        ad: &[u8],
        in_out: &mut [u8],
        plaintext_len: usize,
    ) -> usize {
        assert!(plaintext_len
            .checked_add(TAGLEN)
            .map_or(false, |l| l <= in_out.len()));

        let mut nonce_bytes = [0u8; 12];
        nonce_bytes[4..].copy_from_slice(&nonce.to_le_bytes());
        let nonce = aead::Nonce::assume_unique_for_key(nonce_bytes);

        let key =
            LessSafeKey::new(UnboundKey::new(&aead::CHACHA20_POLY1305, k.as_slice()).unwrap());

        let (in_out, tag_out) = in_out[..plaintext_len + TAGLEN].split_at_mut(plaintext_len);
        let tag = key
            .seal_in_place_separate_tag(nonce, aead::Aad::from(ad), in_out)
            .unwrap();
        tag_out.copy_from_slice(tag.as_ref());

        plaintext_len + TAGLEN
    }

    fn decrypt(
        k: &Self::Key,
        nonce: u64,
        ad: &[u8],
        ciphertext: &[u8],
        out: &mut [u8],
    ) -> Result<(), ()> {
        assert!(ciphertext.len().checked_sub(TAGLEN) == Some(out.len()));

        let mut nonce_bytes = [0u8; 12];
        nonce_bytes[4..].copy_from_slice(&nonce.to_le_bytes());
        let nonce = aead::Nonce::assume_unique_for_key(nonce_bytes);

        let key =
            LessSafeKey::new(UnboundKey::new(&aead::CHACHA20_POLY1305, k.as_slice()).unwrap());
        let mut in_out = ciphertext.to_vec();

        let out0 = key
            .open_in_place(nonce, aead::Aad::from(ad), &mut in_out)
            .map_err(|_| ())?;

        out[..out0.len()].copy_from_slice(out0);
        Ok(())
    }

    fn decrypt_in_place(
        k: &Self::Key,
        nonce: u64,
        ad: &[u8],
        in_out: &mut [u8],
        ciphertext_len: usize,
    ) -> Result<usize, ()> {
        assert!(ciphertext_len <= in_out.len());
        assert!(ciphertext_len >= TAGLEN);

        let mut nonce_bytes = [0u8; 12];
        nonce_bytes[4..].copy_from_slice(&nonce.to_le_bytes());
        let nonce = aead::Nonce::assume_unique_for_key(nonce_bytes);

        let key =
            LessSafeKey::new(UnboundKey::new(&aead::CHACHA20_POLY1305, k.as_slice()).unwrap());
        key.open_in_place(nonce, aead::Aad::from(ad), &mut in_out[..ciphertext_len])
            .map_err(|_| ())?;

        Ok(ciphertext_len - TAGLEN)
    }
}

pub enum Aes256Gcm {}

impl Cipher for Aes256Gcm {
    fn name() -> &'static str {
        "AESGCM"
    }

    type Key = Sensitive<[u8; 32]>;

    fn encrypt(k: &Self::Key, nonce: u64, ad: &[u8], plaintext: &[u8], out: &mut [u8]) {
        assert!(plaintext.len().checked_add(TAGLEN) == Some(out.len()));

        let mut nonce_bytes = [0u8; 12];
        nonce_bytes[4..].copy_from_slice(&nonce.to_be_bytes());
        let nonce = aead::Nonce::assume_unique_for_key(nonce_bytes);

        let key = LessSafeKey::new(UnboundKey::new(&aead::AES_256_GCM, k.as_slice()).unwrap());

        let (in_out, tag_out) = out.split_at_mut(plaintext.len());
        in_out.copy_from_slice(plaintext);

        let tag = key
            .seal_in_place_separate_tag(nonce, aead::Aad::from(ad), in_out)
            .unwrap();
        tag_out.copy_from_slice(tag.as_ref());
    }

    fn encrypt_in_place(
        k: &Self::Key,
        nonce: u64,
        ad: &[u8],
        in_out: &mut [u8],
        plaintext_len: usize,
    ) -> usize {
        assert!(plaintext_len
            .checked_add(TAGLEN)
            .map_or(false, |l| l <= in_out.len()));

        let mut nonce_bytes = [0u8; 12];
        nonce_bytes[4..].copy_from_slice(&nonce.to_be_bytes());
        let nonce = aead::Nonce::assume_unique_for_key(nonce_bytes);

        let key = LessSafeKey::new(UnboundKey::new(&aead::AES_256_GCM, k.as_slice()).unwrap());

        let (in_out, tag_out) = in_out[..plaintext_len + TAGLEN].split_at_mut(plaintext_len);
        let tag = key
            .seal_in_place_separate_tag(nonce, aead::Aad::from(ad), in_out)
            .unwrap();
        tag_out.copy_from_slice(tag.as_ref());

        plaintext_len + TAGLEN
    }

    fn decrypt(
        k: &Self::Key,
        nonce: u64,
        ad: &[u8],
        ciphertext: &[u8],
        out: &mut [u8],
    ) -> Result<(), ()> {
        assert!(ciphertext.len().checked_sub(TAGLEN) == Some(out.len()));

        let mut nonce_bytes = [0u8; 12];
        nonce_bytes[4..].copy_from_slice(&nonce.to_be_bytes());
        let nonce = aead::Nonce::assume_unique_for_key(nonce_bytes);

        let key = LessSafeKey::new(UnboundKey::new(&aead::AES_256_GCM, k.as_slice()).unwrap());
        let mut in_out = ciphertext.to_vec();

        let out0 = key
            .open_in_place(nonce, aead::Aad::from(ad), &mut in_out)
            .map_err(|_| ())?;

        out[..out0.len()].copy_from_slice(out0);
        Ok(())
    }

    fn decrypt_in_place(
        k: &Self::Key,
        nonce: u64,
        ad: &[u8],
        in_out: &mut [u8],
        ciphertext_len: usize,
    ) -> Result<usize, ()> {
        assert!(ciphertext_len <= in_out.len());
        assert!(ciphertext_len >= TAGLEN);

        let mut nonce_bytes = [0u8; 12];
        nonce_bytes[4..].copy_from_slice(&nonce.to_be_bytes());
        let nonce = aead::Nonce::assume_unique_for_key(nonce_bytes);

        let key = LessSafeKey::new(UnboundKey::new(&aead::AES_256_GCM, k.as_slice()).unwrap());
        key.open_in_place(nonce, aead::Aad::from(ad), &mut in_out[..ciphertext_len])
            .map_err(|_| ())?;

        Ok(ciphertext_len - TAGLEN)
    }
}
