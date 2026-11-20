#[derive(PartialEq, Debug)]
enum NameOrId<'a, T: FromStr> {
    Name(&'a SudoString),
    Id(T),
}

impl<'a, T: FromStr> NameOrId<'a, T> {
    pub fn parse(input: &'a SudoString) -> Option<Self> {
        if input.is_empty() {
            None
        } else if let Some(stripped) = input.strip_prefix('#') {
            stripped.parse::<T>().ok().map(|id| Self::Id(id))
        } else {
            Some(Self::Name(input))
        }
    }
}
