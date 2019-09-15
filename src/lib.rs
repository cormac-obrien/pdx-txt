/// A parser for Clausewitz Engine text files
// # Grammar
// ```ebnf
// any = ? any character ? ;
//
// ascii_alpha = ? any ASCII letter ? ;
// ascii_num = ? digits 0-9 ? ;
// ascii_alphanum = ascii_letter | ascii_digit ;
//
// space = " " | "\t" ;
// line_ending = "\r\n" | "\n" ;
// special = "{" | "}" | "=" ;
//
// line_comment = "#" { ? all characters ? - line_ending } line_ending ;
//
// key = { ascii_alphanum | "_" } ;
// text_simple = { any - ( "{" | "}" | "=" ) } ;
// TODO...
// ```
use failure::Fail;
use nom::{
    branch::alt,
    bytes::complete::{escaped, take, take_till, take_while1},
    character::complete::{alphanumeric1, char, digit1, line_ending, one_of, space0, space1},
    combinator::{all_consuming, cut, map, map_res, not, opt, peek, recognize},
    error::{ParseError, VerboseError},
    multi::{fold_many0, many0},
    number::complete::float,
    sequence::{pair, preceded, separated_pair, terminated},
    Err, IResult,
};
use std::{
    collections::HashMap,
    convert::From,
    fmt::{self, Display, Formatter},
    str::FromStr,
};

#[derive(Debug, PartialEq)]
pub enum Error {
    NoSuchProperty(String),
    Parse(String),
    Type { value: OwnedValue, target: String },
}

impl From<(&str, nom::error::VerboseError<&str>)> for Error {
    fn from(from: (&str, nom::error::VerboseError<&str>)) -> Self {
        let (input, error) = from;
        Error::Parse(nom::error::convert_error(input, error))
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Error::NoSuchProperty(ref s) => write!(f, "No such property: {}", s),
            Error::Parse(ref s) => write!(f, "Parse error: {}", s),
            Error::Type { value, target } => {
                write!(f, "Type error: converting {:?} to {}", value, target)
            }
        }
    }
}

impl Fail for Error {}

#[derive(Clone, Debug, PartialEq)]
pub enum Value<'a> {
    Int(i32),
    Float(f32),
    Text(&'a str),
    FlatList(Vec<Value<'a>>), // for multiple identical keys in a property list
    List(Vec<Value<'a>>),
    Object(Properties<'a>),
}

impl<'a> Value<'a> {
    fn to_owned_value(&self) -> OwnedValue {
        match self {
            Value::Int(i) => OwnedValue::Int(*i),
            Value::Float(f) => OwnedValue::Float(*f),
            Value::Text(ref s) => OwnedValue::Text(s.to_string()),
            Value::FlatList(ref fl) => {
                OwnedValue::FlatList(fl.iter().map(|v| v.to_owned_value()).collect())
            }
            Value::List(ref l) => OwnedValue::List(l.iter().map(|v| v.to_owned_value()).collect()),
            Value::Object(ref p) => OwnedValue::Object(p.to_owned_properties()),
        }
    }

    pub fn try_as_int(&self) -> Result<i32, Error> {
        match self {
            Value::Int(i) => Ok(*i),
            x => Err(Error::Type {
                value: x.to_owned_value(),
                target: "i32".to_string(),
            }),
        }
    }

    pub fn try_as_float(&self) -> Result<f32, Error> {
        match self {
            Value::Float(f) => Ok(*f),
            x => Err(Error::Type {
                value: x.to_owned_value(),
                target: "f32".to_string(),
            }),
        }
    }

    pub fn try_as_str(&self) -> Result<&'a str, Error> {
        match self {
            Value::Text(s) => Ok(s),
            x => Err(Error::Type {
                value: x.to_owned_value(),
                target: "&str".to_string(),
            }),
        }
    }

    pub fn try_as_list(&self) -> Result<&[Value<'a>], Error> {
        match self {
            Value::List(v) | Value::FlatList(v) => Ok(v.as_slice()),
            x => Err(Error::Type {
                value: x.to_owned_value(),
                target: "&str".to_string(),
            }),
        }
    }

    pub fn try_as_object(&self) -> Result<&Properties<'a>, Error> {
        match self {
            Value::Object(ref o) => Ok(o),
            x => Err(Error::Type {
                value: x.to_owned_value(),
                target: "&str".to_string(),
            }),
        }
    }
}

impl<'a> From<i32> for Value<'a> {
    fn from(value: i32) -> Self {
        Value::Int(value)
    }
}

impl<'a> From<f32> for Value<'a> {
    fn from(value: f32) -> Self {
        Value::Float(value)
    }
}

impl<'a> From<&'a str> for Value<'a> {
    fn from(from: &'a str) -> Self {
        Value::Text(from)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Properties<'a> {
    map: HashMap<&'a str, Value<'a>>,
}

impl<'a> Properties<'a> {
    pub fn get<S>(&self, key: S) -> Result<&Value<'a>, Error>
    where
        S: AsRef<str>,
    {
        self.map
            .get(key.as_ref())
            .ok_or(Error::NoSuchProperty(key.as_ref().to_string()))
    }

    fn to_owned_properties(&self) -> OwnedProperties {
        OwnedProperties {
            map: self
                .map
                .iter()
                .map(|(k, v)| (k.to_string(), v.to_owned_value()))
                .collect(),
        }
    }
}

#[derive(Clone, Debug)]
struct PropertiesBuilder<'a> {
    map: HashMap<&'a str, Value<'a>>,
}

impl<'a> PropertiesBuilder<'a> {
    fn new() -> PropertiesBuilder<'a> {
        PropertiesBuilder {
            map: HashMap::new(),
        }
    }

    fn insert(&mut self, k: &'a str, v: Value<'a>) {
        if let Some(Value::FlatList(ref mut l)) = self.map.get_mut(k) {
            l.push(v);
        } else if self.map.get(k).is_some() {
            let old_val = self.map.remove(k).unwrap();
            self.map.insert(k, Value::FlatList(vec![old_val, v]));
        } else {
            self.map.insert(k, v);
        }
    }

    fn build(self) -> Properties<'a> {
        Properties { map: self.map }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum OwnedValue {
    Int(i32),
    Float(f32),
    Text(String),
    FlatList(Vec<OwnedValue>),
    List(Vec<OwnedValue>),
    Object(OwnedProperties),
}

#[derive(Clone, Debug, PartialEq)]
pub struct OwnedProperties {
    map: HashMap<String, OwnedValue>,
}

// consume line comments (excluding the line ending)
fn line_comment<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&str, &str, E> {
    preceded(char('#'), take_till(|c| c == '\r' || c == '\n'))(input)
}

// consume spaces, line endings and comments
fn space_line_comment<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&str, Vec<&str>, E> {
    many0(alt((space1, line_ending, line_comment)))(input)
}

// like line_ending, but also eats trailing spaces and comments
fn trailing_line_ending<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&str, &str, E> {
    preceded(many0(space1), preceded(opt(line_comment), line_ending))(input)
}

fn save_header<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&str, &str, E> {
    terminated(alphanumeric1, line_ending)(input)
}

fn integer<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&str, i32, E> {
    map_res(
        recognize(terminated(pair(opt(char('-')), digit1), not(char('.')))),
        FromStr::from_str,
    )(input)
}

fn floating<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&str, f32, E> {
    // check first char is a digit
    // this avoids weird parse issues with words that start with the letter e
    preceded(peek(digit1), terminated(float, peek(not(char('.')))))(input)
}

fn is_text_special(c: char) -> bool {
    c.is_whitespace() || "{}=\"".contains(c)
}

fn text_simple<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&str, &str, E> {
    take_while1(|c| !is_text_special(c))(input)
}

fn text_quoted_normal<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&str, &str, E> {
    take_while1(|c| c != '\\' && c != '"')(input)
}

fn text_quoted_inner<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&str, &str, E> {
    escaped(text_quoted_normal, '\\', one_of("\"nr\\"))(input)
}

fn text_quoted<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&str, &str, E> {
    preceded(
        char('\"'),
        cut(terminated(
            map(opt(text_quoted_inner), |o| o.unwrap_or("")),
            char('\"'),
        )),
    )(input)
}

fn text<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&str, &str, E> {
    preceded(space0, alt((text_quoted, text_simple)))(input)
}

fn lbrace<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&str, char, E> {
    preceded(space_line_comment, char('{'))(input)
}

fn rbrace<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&str, char, E> {
    preceded(space_line_comment, char('}'))(input)
}

fn list_item<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&str, Value<'a>, E> {
    preceded(space_line_comment, property_rvalue)(input)
}

fn list<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&str, Vec<Value<'a>>, E> {
    preceded(lbrace, terminated(many0(list_item), rbrace))(input)
}

fn property_rvalue<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&str, Value<'a>, E> {
    alt((
        map(integer, Value::Int),
        map(floating, Value::Float),
        map(text, Value::Text),
        map(list, Value::List),
        map(object, Value::Object),
    ))(input)
}

// sometimes saves have empty braces with no associated key
fn empty_property<'a, E: ParseError<&'a str>>(
    input: &'a str,
) -> IResult<&str, (&str, Value<'a>), E> {
    map(preceded(lbrace, rbrace), |_| ("", "".into()))(input)
}

fn property<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&str, (&str, Value<'a>), E> {
    separated_pair(
        text,
        preceded(space0, opt(char('='))), // save files sometimes don't have the equal
        preceded(space0, property_rvalue),
    )(input)
}

fn properties<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&str, Properties<'a>, E> {
    map(
        fold_many0(
            preceded(
                space_line_comment,
                terminated(
                    alt((property, empty_property)),
                    // properties separated by spaces instead of lines occur in saves
                    alt((
                        trailing_line_ending,
                        space1,
                        map(not(peek(take(1usize))), |_| ""), // EOF
                    )),
                ),
            ),
            PropertiesBuilder::new(),
            |mut pb, (k, v)| {
                if k != "" {
                    println!("{} = {:?}", k, &v);
                    pb.insert(k, v);
                }
                pb
            },
        ),
        move |pb| pb.build(),
    )(input)
}

fn object<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&str, Properties<'a>, E> {
    // TODO: move cut(lbrace) to a scope() parser
    preceded(lbrace, terminated(properties, cut(rbrace)))(input)
}

fn root<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&str, Properties<'a>, E> {
    all_consuming(preceded(
        opt(save_header),
        terminated(properties, space_line_comment),
    ))(&input)
}

pub fn parse(input: &str) -> Result<Properties, Error> {
    match root::<VerboseError<&str>>(input) {
        Err(Err::Error(e)) | Err(Err::Failure(e)) => Err(Error::from((input, e))),
        Ok(("", p)) => Ok(p),

        Err(_) => unreachable!("incomplete"),
        Ok((_, _)) => unreachable!("input remaining"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_integer() {
        assert_eq!(integer::<()>("123"), Ok(("", 123)));
        assert_eq!(integer::<()>("-456"), Ok(("", -456)));
        assert_eq!(opt(integer::<()>)("175.012"), Ok(("175.012", None)));
    }

    #[test]
    fn test_floating() {
        assert_eq!(opt(floating::<()>)("1970.1.1"), Ok(("1970.1.1", None)));
    }

    #[test]
    fn test_text_simple() {
        assert_eq!(text_simple::<()>("a.val ue"), Ok((" ue", "a.val")));
    }

    #[test]
    fn test_text_quoted() {
        assert_eq!(opt(text_quoted::<()>)("a text"), Ok(("a text", None)));
        assert_eq!(text_quoted::<()>("\"a text\""), Ok(("", "a text")));
        assert_eq!(
            text_quoted::<()>("\"a \\\"text\\\"\""),
            Ok(("", "a \\\"text\\\""))
        );
    }

    #[test]
    fn test_lbrace() {
        assert_eq!(lbrace::<()>("{"), Ok(("", '{')));
        assert_eq!(lbrace::<()>("{ after"), Ok((" after", '{')));
        assert_eq!(lbrace::<()>("  \t {"), Ok(("", '{')));
    }

    #[test]
    fn test_list_item() {
        assert_eq!(
            list_item::<()>("  \n \r\n\t  \titem"),
            Ok(("", "item".into()))
        );
    }

    #[test]
    fn test_list() {
        assert_eq!(
            list::<()>("{ item1 item2 item3 }"),
            Ok(("", vec!["item1".into(), "item2".into(), "item3".into(),]))
        );
        assert_eq!(
            list::<()>("{\nitem1\r\nitem2 \n\n\titem3\r\n \t}"),
            Ok(("", vec!["item1".into(), "item2".into(), "item3".into(),]))
        );
    }

    #[test]
    fn test_properties() {
        let list = r#"# comment
key1 = val1
key2=e
key3 = val3
"#;

        assert_eq!(
            properties::<()>(list),
            Ok((
                "",
                Properties {
                    map: [
                        ("key1", Value::Text("val1")),
                        ("key2", Value::Text("e")), // ensure this doesn't get interpreted as float
                        ("key3", Value::Text("val3")),
                    ]
                    .iter()
                    .cloned()
                    .collect()
                }
            ))
        );
    }

    #[test]
    fn test_parse() {
        let txt = r#" #comment
root_key = {
    prop1_key = val1
    prop2_key = { 0.000 2.722 1.870 }
    prop3_key = { # prop3 comment
        prop3_1_key = val3_1
    }
}
"#;
        let obj = Properties {
            map: [(
                "root_key",
                Value::Object(Properties {
                    map: [
                        ("prop1_key", Value::Text("val1")),
                        (
                            "prop2_key",
                            Value::List(vec![0.000.into(), 2.722.into(), 1.870.into()]),
                        ),
                        (
                            "prop3_key",
                            Value::Object(Properties {
                                map: [("prop3_1_key", Value::Text("val3_1"))]
                                    .iter()
                                    .cloned()
                                    .collect(),
                            }),
                        ),
                    ]
                    .iter()
                    .cloned()
                    .collect(),
                }),
            )]
            .iter()
            .cloned()
            .collect(),
        };

        assert_eq!(parse(txt), Ok(obj))
    }

    #[test]
    fn test_properties_get() {
        let mut pb = PropertiesBuilder::new();
        pb.insert("key1", Value::Text("value1"));
        pb.insert("key2", Value::Text("k2v1"));
        pb.insert("key2", Value::Text("k2v2"));
        pb.insert(
            "key3",
            Value::List(vec!["k3v1".into(), "k3v2".into(), "k3v3".into()]),
        );
        pb.insert(
            "key4",
            Value::Object(Properties {
                map: [("k4_1", Value::Text("v4_1"))].iter().cloned().collect(),
            }),
        );
        let p = pb.build();
        assert_eq!(p.get("key1"), Ok(&Value::Text("value1")));
        assert_eq!(
            p.get("key2"),
            Ok(&Value::FlatList(vec!["k2v1".into(), "k2v2".into()]))
        );
        assert_eq!(
            p.get("key3"),
            Ok(&Value::List(vec![
                "k3v1".into(),
                "k3v2".into(),
                "k3v3".into()
            ]))
        );
        assert_eq!(
            p.get("key4"),
            Ok(&Value::Object(Properties {
                map: [("k4_1", Value::Text("v4_1"))].iter().cloned().collect(),
            }))
        );
    }
}
