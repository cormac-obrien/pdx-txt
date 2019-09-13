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
    character::complete::{alphanumeric1, char, line_ending, one_of, space0, space1},
    combinator::{all_consuming, cut, map, not, opt, peek},
    error::{ParseError, VerboseError},
    multi::{fold_many0, many0},
    sequence::{preceded, separated_pair, terminated},
    Err, IResult,
};
use std::{
    collections::HashMap,
    convert::From,
    fmt::{self, Display, Formatter},
};

#[derive(Debug, PartialEq)]
pub struct Error(String);

impl From<(&str, nom::error::VerboseError<&str>)> for Error {
    fn from(from: (&str, nom::error::VerboseError<&str>)) -> Self {
        let (input, error) = from;
        Error(nom::error::convert_error(input, error))
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "Parse error: {}", self.0)
    }
}

impl Fail for Error {}

#[derive(Clone, Debug, PartialEq)]
pub enum Value<'a> {
    Text(&'a str),
    List(Vec<Value<'a>>),
    Object(Properties<'a>),
}

impl<'a> From<&'a str> for Value<'a> {
    fn from(from: &'a str) -> Self {
        Value::Text(from)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Properties<'a> {
    Map(HashMap<&'a str, Value<'a>>),
    List(Vec<(&'a str, Value<'a>)>),
}

#[derive(Clone, Debug)]
struct PropertiesBuilder<'a> {
    has_duplicates: bool,
    map: HashMap<&'a str, Value<'a>>,
    list: Vec<(&'a str, Value<'a>)>,
}

impl<'a> PropertiesBuilder<'a> {
    fn new() -> PropertiesBuilder<'a> {
        PropertiesBuilder {
            has_duplicates: false,
            map: HashMap::new(),
            list: Vec::new(),
        }
    }

    fn insert(&mut self, k: &'a str, v: Value<'a>) {
        if !self.has_duplicates && self.map.insert(k, v.clone()).is_some() {
            self.has_duplicates = true;
        }

        self.list.push((k, v));
    }

    fn build(self) -> Properties<'a> {
        if self.has_duplicates {
            Properties::List(self.list)
        } else {
            Properties::Map(self.map)
        }
    }
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
                    pb.insert(k, v);
                }
                pb
            },
        ),
        move |pb| pb.build(),
    )(input)
}

fn object<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&str, Properties<'a>, E> {
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
    fn test_text_simple() {
        assert_eq!(text_simple::<()>("123"), Ok(("", "123")));
        assert_eq!(text_simple::<()>("123 456"), Ok((" 456", "123")));
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
key2 = val2
key3 = val3
"#;

        assert_eq!(
            properties::<()>(list),
            Ok((
                "",
                Properties::Map(
                    [
                        ("key1", Value::Text("val1")),
                        ("key2", Value::Text("val2")),
                        ("key3", Value::Text("val3")),
                    ]
                    .iter()
                    .cloned()
                    .collect()
                )
            ))
        );
    }

    #[test]
    fn test_parse() {
        let txt = r#" #comment
root_key = {
    prop1_key = val1
    prop2_key = { val2a val2b val2c }
    prop3_key = { # prop3 comment
        prop3_1_key = val3_1
    }
}
"#;
        let obj = Properties::Map(
            [(
                "root_key",
                Value::Object(Properties::Map(
                    [
                        ("prop1_key", Value::Text("val1")),
                        (
                            "prop2_key",
                            Value::List(vec!["val2a".into(), "val2b".into(), "val2c".into()]),
                        ),
                        (
                            "prop3_key",
                            Value::Object(Properties::Map(
                                [("prop3_1_key", Value::Text("val3_1"))]
                                    .iter()
                                    .cloned()
                                    .collect(),
                            )),
                        ),
                    ]
                    .iter()
                    .cloned()
                    .collect(),
                )),
            )]
            .iter()
            .cloned()
            .collect(),
        );

        assert_eq!(parse(txt), Ok(obj))
    }
}
