impl UserId {
    pub fn new(id: libc::uid_t) -> Self {
        Self(id)
    }

    pub fn inner(&self) -> libc::uid_t {
        self.0
    }

    pub const ROOT: Self = Self(0);
}
