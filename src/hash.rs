use aws_lc_rs::digest;
use noise_protocol::Hash;

pub struct Sha256 {
    context: digest::Context,
}

pub struct Sha512 {
    context: digest::Context,
}

impl Default for Sha256 {
    fn default() -> Sha256 {
        Sha256 {
            context: digest::Context::new(&digest::SHA256),
        }
    }
}

impl Hash for Sha256 {
    type Block = [u8; 64];
    type Output = [u8; 32];

    fn name() -> &'static str {
        "SHA256"
    }

    fn input(&mut self, data: &[u8]) {
        self.context.update(data);
    }

    fn result(&mut self) -> Self::Output {
        let mut out = [0u8; 32];
        // XXX have to clone becuase finish() moves Context.
        out.copy_from_slice(self.context.clone().finish().as_ref());
        out
    }
}

impl Default for Sha512 {
    fn default() -> Sha512 {
        Sha512 {
            context: digest::Context::new(&digest::SHA512),
        }
    }
}

impl Hash for Sha512 {
    type Block = [u8; 128];
    type Output = [u8; 64];

    fn name() -> &'static str {
        "SHA512"
    }

    fn input(&mut self, data: &[u8]) {
        self.context.update(data);
    }

    fn result(&mut self) -> Self::Output {
        let mut out = [0u8; 64];
        out.copy_from_slice(self.context.clone().finish().as_ref());
        out
    }
}
