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
extern crate nom;

use nom::{
    branch::alt,
    bytes::complete::{escaped, take_till, take_while, take_while1},
    character::complete::{char, line_ending, one_of, space0, space1},
    combinator::{cut, map, opt},
    multi::{fold_many0, many0},
    sequence::{preceded, separated_pair, terminated},
    IResult,
};
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq)]
pub enum Value<'a> {
    Text(&'a str),
    List(Vec<&'a str>),
    Object(Properties<'a>),
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
fn line_comment(input: &str) -> IResult<&str, &str> {
    preceded(char('#'), take_till(|c| c == '\r' || c == '\n'))(input)
}

// consume spaces, line endings and comments
fn space_line_comment(input: &str) -> IResult<&str, Vec<&str>> {
    many0(alt((space1, line_ending, line_comment)))(input)
}

// like line_ending, but also eats trailing spaces and comments
fn space_comment_line_ending(input: &str) -> IResult<&str, Option<&str>> {
    preceded(many0(space1), opt(line_ending))(input)
}

fn key(input: &str) -> IResult<&str, &str> {
    take_while(|item: char| item.is_ascii_alphanumeric() || item == '_')(input)
}

fn is_text_special(c: char) -> bool {
    c.is_whitespace() || "{}=\"".contains(c)
}

fn text_simple(input: &str) -> IResult<&str, &str> {
    take_while1(|c| !is_text_special(c))(input)
}

fn text_quoted_normal(input: &str) -> IResult<&str, &str> {
    take_while1(|c| c != '\\' && c != '"')(input)
}

fn text_quoted_inner(input: &str) -> IResult<&str, &str> {
    escaped(text_quoted_normal, '\\', one_of("\"nr\\"))(input)
}

fn text_quoted(input: &str) -> IResult<&str, &str> {
    preceded(char('\"'), cut(terminated(text_quoted_inner, char('\"'))))(input)
}

fn text(input: &str) -> IResult<&str, &str> {
    preceded(space0, alt((text_quoted, text_simple)))(input)
}

fn lbrace(input: &str) -> IResult<&str, char> {
    preceded(space_line_comment, char('{'))(input)
}

fn rbrace(input: &str) -> IResult<&str, char> {
    preceded(space_line_comment, char('}'))(input)
}

fn list_item(input: &str) -> IResult<&str, &str> {
    preceded(space_line_comment, text)(input)
}

fn list(input: &str) -> IResult<&str, Vec<&str>> {
    preceded(lbrace, terminated(many0(list_item), rbrace))(input)
}

fn property_rvalue<'a>(input: &'a str) -> IResult<&str, Value<'a>> {
    alt((
        map(text, Value::Text),
        map(list, Value::List),
        map(object, Value::Object),
    ))(input)
}

fn property<'a>(input: &'a str) -> IResult<&str, (&str, Value<'a>)> {
    separated_pair(
        key,
        preceded(space0, char('=')),
        preceded(space0, property_rvalue),
    )(input)
}

fn properties<'a>(input: &'a str) -> IResult<&str, Properties<'a>> {
    map(
        fold_many0(
            preceded(
                space_line_comment,
                terminated(property, space_comment_line_ending),
            ),
            PropertiesBuilder::new(),
            |mut pb, (k, v)| {
                pb.insert(k, v);
                pb
            },
        ),
        move |pb| pb.build(),
    )(input)
}

fn object<'a>(input: &'a str) -> IResult<&str, Properties<'a>> {
    preceded(lbrace, terminated(properties, rbrace))(input)
}

pub fn parse<'a>(input: &'a str) -> IResult<&str, Properties<'a>> {
    terminated(properties, space_line_comment)(input)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_key() {
        assert_eq!(key("a_key"), Ok(("", "a_key")));
        assert_eq!(key("key_1 key_2"), Ok((" key_2", "key_1")));
    }

    #[test]
    fn test_text_simple() {
        assert_eq!(text_simple("123"), Ok(("", "123")));
        assert_eq!(text_simple("123 456"), Ok((" 456", "123")));
        assert_eq!(text_simple("a.val ue"), Ok((" ue", "a.val")));
    }

    #[test]
    fn test_text_quoted() {
        assert_eq!(opt(text_quoted)("a text"), Ok(("a text", None)));
        assert_eq!(text_quoted("\"a text\""), Ok(("", "a text")));
        assert_eq!(
            text_quoted("\"a \\\"text\\\"\""),
            Ok(("", "a \\\"text\\\""))
        );
    }

    #[test]
    fn test_lbrace() {
        assert_eq!(lbrace("{"), Ok(("", '{')));
        assert_eq!(lbrace("{ after"), Ok((" after", '{')));
        assert_eq!(lbrace("  \t {"), Ok(("", '{')));
    }

    #[test]
    fn test_list_item() {
        assert_eq!(list_item("  \n \r\n\t  \titem"), Ok(("", "item")));
    }

    #[test]
    fn test_list() {
        assert_eq!(
            list("{ item1 item2 item3 }"),
            Ok(("", vec!["item1", "item2", "item3",]))
        );
        assert_eq!(
            list("{\nitem1\r\nitem2 \n\n\titem3\r\n \t}"),
            Ok(("", vec!["item1", "item2", "item3",]))
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
            properties(list),
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
                        ("prop2_key", Value::List(vec!["val2a", "val2b", "val2c"])),
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

        assert_eq!(parse(txt), Ok(("", obj)))
    }
}
