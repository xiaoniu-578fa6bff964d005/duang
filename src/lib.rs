//! Rust doesn't support default function arguments and named function arguments.
//!
//! This crate generate an macro interface for a given function that can be invoked with named arguments and fill the default argument, meanwhile keep the old function intact.
//!
//! # Generating macro interface
//!
//! In order to generate macro for a function, we just need to wrap the definition with `duang!{...}`.
//!
//! ```
//! use duang::duang;
//!
//! # const IGNORE: &str = stringify! {
//! duang!(
//! pub fn foo<T>(a: T,b: f64 = 13.0, c: T = a*a) -> (T,f64,T)
//! # )
//! # };
//! # pub fn foo<T>(a: T,b: f64, c: T) -> (T,f64,T)
//! where
//!   T: std::ops::Mul<T, Output = T>,
//!   T: std::fmt::Display,
//!   T: Copy,
//! {
//!   (a,b,c)
//! }
//! # const IGNORE2: &str = stringify! {
//! # (
//! );
//! # };
//! # fn main() {}
//! ```
//!
//! # Invoke
//!
//! ```
//! # fn main() {
//! use demo_duang::foo;
//! // pass
//! assert_eq!(foo!(1, c = 30, b = -2.0), (1, -2.0, 30));
//! // pass
//! assert_eq!(foo!(a = 10), (10, 13.0, 100));
//! // fail
//! // foo!(1,c=30,c=2);
//! # }
//! ```
//!
//! # Features
//! - Support generics, existensial type.
//! - Friendly error message.
//!
//! # Common issues
//! ## Use local variable in default value.
//! In order to use the generated macro in other crate, users should add `$crate` and path of the variable used.
//! Also, the variable should be visible(`pub`) for the scope where the macro is invoked.
//!
//! ```
//! mod bar {
//!   use duang::duang;
//!   pub static NUM: i32 = 42;
//!   duang!(
//!   pub fn foo(a: i32 = $crate::bar::NUM) -> i32 { a }
//!   );
//! }
//! fn main() {
//!   use bar::foo;
//!   assert_eq!(foo!(), 42);
//! }
//! ```
//!
//!
//! # Limitations
//! - Don't support associated function.
//! - Wildchar can not be used in pattern argument. For example `fn foo((a,_): (i32, i32))` is illegal.
//!
//! # TODO
//! - Generate document for function or macro.
//! - After "Attributes in formal function parameter position"([#60406](https://github.com/rust-lang/rust/issues/60406)) stabilize, change function-like macros to attribute-like macros.

#![recursion_limit = "128"]

extern crate proc_macro;

use argument::*;
use enum_hack::*;
use error::*;
use proc_macro2::*;
use quote::*;
use syn::punctuated::*;
use syn::spanned::*;
use syn::token::Brace;
use syn::{parse_macro_input, Token};
use syn::{Block, Expr, ExprVerbatim, Pat, PatIdent, Stmt, Type};
use syn_default_parameter_patch::FnArg::*;
use syn_default_parameter_patch::{ArgCaptured, FnArg, ItemFn};

/// The whole point.
#[proc_macro]
pub fn duang(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
  // eprintln!("original function: \"{}\"", &input);
  let mut input = parse_macro_input!(input as ItemFn);
  let input_copy = input.clone();
  let ident = input.ident.clone();

  let args = &mut input.decl.inputs;

  // check
  // check only Captured argument and all mandatory parameters are all ahead of default ones.
  let (_mandatory_args, mut default_args) = match split_args(args) {
    Ok(t) => t,
    Err(errors) => return (quote!(#(#errors)*)).into(),
  };

  let pub_use = quote! {
    extern crate duang;
    pub use duang::DuangHack;
  };

  let macro_define = {
    let enum_item = {
      let args = &input_copy.decl.inputs;

      // TODO: hygiene
      let eh = EnumHack {
        name: Ident::new(&format!("__{}_duang_enum_hack2", ident), Span::call_site()),
        token_streams: vec![quote!($($l)*), quote!(#args)],
      };
      quote! {
        #pub_use

        #[derive(DuangHack)]
        #eh
      }
    };

    let fill_function = {
      let mut fill_fun = input_copy;
      let fill_ident = Ident::new("fill", Span::call_site());
      let mut unwrap_blocks = Vec::new();
      let mut params = Vec::new();

      {
        let args = &mut fill_fun.decl.inputs;

        for (i, ca) in args
          .iter_mut()
          .map(|arg| match arg {
            Captured(ca) => ca,
            _ => unimplemented!(),
          })
          .enumerate()
        {
          // TODO: hygiene
          let dummy_ident = ident_by_index(i, Span::call_site());

          params.push((&ca.pat).into_token_stream());
          let pat = (&ca.pat).into_token_stream();
          if let Some(ref dv) = ca.dv {
            // add unwrap block.
            let dv = (&dv.val).into_token_stream();
            unwrap_blocks.push(quote! {
              let #pat = #dummy_ident.unwrap_or(#dv);
            });

            // wrap type with Option and remove default params.
            let ty = &ca.ty;
            let tyts = quote! {::std::option::Option<#ty>}.into();
            ca.ty = parse_macro_input!(tyts as Type);
            ca.pat = Pat::Ident(PatIdent {
              ident: dummy_ident,
              by_ref: None,
              mutability: None,
              subpat: None,
            });
            ca.dv.take();
          }
        }
      }
      // change name
      fill_fun.ident = fill_ident;
      // change body
      // TODO: hygiene
      let body = quote! {
        {
          #(#unwrap_blocks)*
          // $crate::#ident(#(#params),*)
          #ident(#(#params),*)
        }
      };
      fill_fun.block = Box::new(Block {
        brace_token: Brace {
          span: Span::call_site(),
        },
        stmts: vec![Stmt::Expr(Expr::Verbatim(ExprVerbatim { tts: body }))],
      });

      quote! {
        #[inline]
        #fill_fun
      }
    };

    quote! {
      #[macro_export]
      macro_rules! #ident {
        ($($l:tt)*) => {
          {
          #fill_function

          #enum_item

          call_fill!()
          }
        }
      }
    }
  };

  // change original parameter in function declaration.
  for arg in default_args.iter_mut() {
    arg.dv.take();
  }

  let origin_function = input.into_token_stream();

  // TODO: hygiene
  let hack = enum_hack::wrap_in_enum_hack(
    &format!("__{}_duang_enum_hack", ident),
    vec![quote!(#macro_define)],
  );

  let result = quote!(#origin_function #hack);
  // eprintln!("expand with duang!: \"{}\"", &result);
  result.into()
}

#[doc(hidden)]
#[proc_macro_derive(ExpandEnumHack)]
pub fn expand_enum_hack(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
  let eh = parse_macro_input!(input as EnumHack);
  let tss = eh.token_streams;
  let result = quote!(#(#tss)*);
  // eprintln!("derive with ExpandEnumHack: {}", &result);
  result.into()
}

#[doc(hidden)]
#[proc_macro_derive(DuangHack)]
pub fn duang_hack(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
  let eh = parse_macro_input!(input as EnumHack);
  let mut tss = eh.token_streams.into_iter();
  let inputs = tss.next().unwrap().into();
  // eprintln!("inputs: {}", &inputs);
  let args = tss.next().unwrap().into();
  // eprintln!("args: {}", &args);

  let inputs = parse_macro_input!(inputs as InputArguments);
  // eprintln!("inputs: {}", (&inputs).into_token_stream());
  let args = parse_macro_input!(args as FnArgs);
  // eprintln!("args: {}", (&args).into_token_stream());

  let body = get_macro_body(inputs, args);

  let result = quote!(
  macro_rules! call_fill {
    () => {
      {
        #body
      }
    }
  };
  );
  // eprintln!("args: {}", &result);
  result.into()
}

fn get_macro_body(mut inputs: InputArguments, mut args: FnArgs) -> TokenStream {
  // check inputs can be divide by two part.
  let (inu, inn) = match split_inputs(&mut inputs.args) {
    Ok(t) => t,
    Err(errors) => return quote!(#(#errors)*),
  };

  // check args can be divide by two part.
  let (aru, arn) = match split_args(&mut args.args) {
    Ok(t) => t,
    Err(errors) => return quote!(#(#errors)*),
  };

  let lenu = aru.len();
  let lenn = arn.len();
  let args = args
    .args
    .iter()
    .map(|arg| match arg {
      Captured(ca) => ca,
      _ => unimplemented!(),
    })
    .collect::<Vec<_>>();

  use std::collections::HashMap;
  let mut index_map = HashMap::new();
  let mut slot = vec![None; lenu + lenn];
  let mut errors = Vec::new();

  // build index_map
  for (i, arg) in args.iter().enumerate() {
    use std::collections::hash_map::Entry;
    match index_map.entry(&arg.pat) {
      Entry::Occupied(_entry) => {
        // should not happend, because original function is illegal and will not pass to this macro.
        unreachable!()
      }
      Entry::Vacant(entry) => entry.insert(i),
    };
  }
  // fill the params, meanwhile chack conflicts.
  for (i, a) in inu.iter().enumerate() {
    slot[i] = Some(InputArgument::Unnamed((*a).clone()));
  }
  for a in inn.iter() {
    let i = index_map[&a.pat];
    let data = InputArgument::Named((*a).clone());
    match &mut slot[i] {
      Some(former_a) => {
        // assign conflict
        errors.push(error(
          "This argument is assigned more than once.",
          Spanned::span(&data),
        ));
        errors.push(error("Previously assigned here", Spanned::span(former_a)));
      }
      None => slot[i] = Some(data),
    }
  }
  // check all mandatoy parameters are filled.
  for (i, a) in slot[0..lenu].iter().enumerate() {
    match a {
      Some(arg) => match arg {
        InputArgument::Named(inn) => {
          if inn.val.is_none() {
            errors.push(error(
              "Mandatory argument is not assigned a value.",
              Spanned::span(arg),
            ));
          }
        }
        _ => {}
      },
      None => {
        errors.push(error(
          "Mandatory argument is not assigned.",
          Spanned::span(args[i]),
        ));
      }
    };
  }
  if !errors.is_empty() {
    return quote!(#(#errors)*);
  }

  // generate parameters.
  let mut params = Vec::new();
  for a in slot[0..lenu].iter() {
    let expr = match a.as_ref().unwrap() {
      InputArgument::Unnamed(inu) => &inu.expr,
      InputArgument::Named(inn) => &inn.val.as_ref().unwrap().expr,
    };
    params.push(quote!(#expr))
  }
  for a in slot[lenu..].iter() {
    let param = a
      .as_ref()
      .map(|a| {
        let (oexpr, oty) = match a {
          InputArgument::Unnamed(inu) => (Some(&inu.expr), None),
          InputArgument::Named(inn) => (
            inn.val.as_ref().map(|x| &x.expr),
            inn.ty.as_ref().map(|x| &x.ty),
          ),
        };
        if let Some(ty) = oty {
          if let Some(expr) = oexpr {
            quote!(std::option::Option::<#ty>::Some(#expr))
          } else {
            quote!(std::option::Option::<#ty>::None)
          }
        } else {
          let expr = oexpr.unwrap();
          quote!(std::option::Option::Some(#expr))
        }
      })
      .unwrap_or(quote!(std::option::Option::None));
    params.push(param)
  }

  quote!(fill(#(#params),*))
}

fn split_inputs(
  inputs: &mut Punctuated<InputArgument, Token![,]>,
) -> std::result::Result<
  (Vec<&mut UnnamedInputArgument>, Vec<&mut NamedInputArgument>),
  Vec<TokenStream>,
> {
  let mut errors = Vec::new();
  let args = inputs.into_iter();

  let mut inu = Vec::new();
  let mut inn = Vec::new();
  let mut mandatory_now = true;
  for arg in args {
    match arg {
      InputArgument::Unnamed(uia) => {
        if !mandatory_now {
          errors.push(error(
            "Unnamed parameter must be ahead of named parameter.",
            Spanned::span(&uia.expr),
          ));
        } else {
          inu.push(uia);
        }
      }
      InputArgument::Named(nia) => {
        mandatory_now = false;
        inn.push(nia)
      }
    };
  }

  if errors.is_empty() {
    Ok((inu, inn))
  } else {
    Err(errors)
  }
}

fn split_args(
  inputs: &mut Punctuated<FnArg, Token![,]>,
) -> std::result::Result<(Vec<&mut ArgCaptured>, Vec<&mut ArgCaptured>), Vec<TokenStream>> {
  let mut errors = Vec::new();
  let args = inputs.into_iter();

  let mut inu = Vec::new();
  let mut inn = Vec::new();
  let mut mandatory_now = true;
  for arg in args {
    let arg = match arg {
      Captured(ca) => ca,
      SelfRef(_) | SelfValue(_) => {
        errors.push(error(
          "Associated function is not supported yet.",
          Spanned::span(&arg),
        ));
        continue;
      }
      Inferred(_) => {
        errors.push(error(
          "Inferred argument is not supported yet.",
          Spanned::span(&arg),
        ));
        continue;
      }
      Ignored(_) => {
        errors.push(error(
          "Ignored argument is not supported yet.",
          Spanned::span(&arg),
        ));
        continue;
      }
    };
    if arg.dv.is_none() {
      if !mandatory_now {
        errors.push(error(
          "Mandatory parameter must be ahead of default parameter.",
          Spanned::span(&arg),
        ));
      } else {
        inu.push(arg);
      }
    } else {
      mandatory_now = false;
      inn.push(arg)
    }
  }

  if errors.is_empty() {
    Ok((inu, inn))
  } else {
    Err(errors)
  }
}

use syn::Ident;
fn ident_by_index(index: usize, span: Span) -> Ident {
  Ident::new(&format!("__arg_for_fill_{}", index), span)
}

mod syn_default_parameter_patch {
  use attr::FilterAttrs;
  use proc_macro2::*;
  use quote::*;
  use std::hash::{Hash, Hasher};
  use std::iter::FromIterator;
  use syn::parse::*;
  use syn::punctuated::*;
  use tt::TokenStreamHelper;

  use syn::parse2;
  use syn::{braced, parenthesized, Token};
  use syn::{punctuated, token};
  use syn::{
    Abi, ArgSelf, ArgSelfRef, Attribute, Block, Generics, Pat, ReturnType, Type, TypeVerbatim,
    Visibility, WhereClause,
  };
  use FnArg::*;

  /// A free-standing function: `fn process(n: usize) -> Result<()> { ...
  /// }`.
  ///
  /// *This type is available if Syn is built with the `"full"` feature.*
  #[derive(PartialEq, Eq, Clone, Debug, Hash)]
  pub struct ItemFn {
    pub attrs: Vec<Attribute>,
    pub vis: Visibility,
    pub constness: Option<Token![const]>,
    pub unsafety: Option<Token![unsafe]>,
    pub asyncness: Option<Token![async]>,
    pub abi: Option<Abi>,
    pub ident: Ident,
    pub decl: Box<FnDecl>,
    pub block: Box<Block>,
  }

  /// Header of a function declaration, without including the body.
  ///
  /// *This type is available if Syn is built with the `"full"` feature.*
  #[derive(PartialEq, Eq, Clone, Debug, Hash)]
  pub struct FnDecl {
    pub fn_token: Token![fn],
    pub generics: Generics,
    pub paren_token: token::Paren,
    pub inputs: Punctuated<FnArg, Token![,]>,
    pub variadic: Option<Token![...]>,
    pub output: ReturnType,
  }

  /// An argument in a function signature: the `n: usize` in `fn f(n: usize)`.
  ///
  /// *This type is available if Syn is built with the `"full"` feature.*
  ///
  /// # Syntax tree enum
  ///
  /// This type is a [syntax tree enum].
  ///
  /// [syntax tree enum]: enum.Expr.html#syntax-tree-enums
  #[derive(PartialEq, Eq, Clone, Debug, Hash)]
  pub enum FnArg {
    /// Self captured by reference in a function signature: `&self` or `&mut
    /// self`.
    ///
    /// *This type is available if Syn is built with the `"full"` feature.*
    SelfRef(ArgSelfRef),

    /// Self captured by value in a function signature: `self` or `mut
    /// self`.
    ///
    /// *This type is available if Syn is built with the `"full"` feature.*
    SelfValue(ArgSelf),

    /// An explicitly typed pattern captured by a function signature.
    ///
    /// *This type is available if Syn is built with the `"full"` feature.*
    Captured(ArgCaptured),

    /// A pattern whose type is inferred captured by a function signature.
    #[allow(dead_code)]
    Inferred(Pat),
    /// A type not bound to any pattern in a function signature.
    Ignored(Type),
  }

  #[derive(PartialEq, Eq, Clone, Debug, Hash)]
  pub struct ArgCaptured {
    pub pat: Pat,
    pub colon_token: Token![:],
    pub ty: Type,
    pub dv: Option<DefaultValue>,
  }

  /// DefaultValue part of a parameter.
  ///
  /// *This type is available if Syn is built with the `"full"` feature.*
  #[derive(Clone, Debug)]
  pub struct DefaultValue {
    pub eq: Token![=],
    pub val: TokenStream,
  }

  impl PartialEq for DefaultValue {
    fn eq(&self, other: &Self) -> bool {
      TokenStreamHelper(&self.val) == TokenStreamHelper(&other.val)
    }
  }
  impl Eq for DefaultValue {}
  impl Hash for DefaultValue {
    fn hash<H>(&self, state: &mut H)
    where
      H: Hasher,
    {
      TokenStreamHelper(&self.val).hash(state);
    }
  }

  mod tt {
    use std::hash::{Hash, Hasher};

    use proc_macro2::{Delimiter, TokenStream, TokenTree};

    pub struct TokenTreeHelper<'a>(pub &'a TokenTree);

    impl<'a> PartialEq for TokenTreeHelper<'a> {
      fn eq(&self, other: &Self) -> bool {
        use proc_macro2::Spacing;

        match (self.0, other.0) {
          (&TokenTree::Group(ref g1), &TokenTree::Group(ref g2)) => {
            match (g1.delimiter(), g2.delimiter()) {
              (Delimiter::Parenthesis, Delimiter::Parenthesis)
              | (Delimiter::Brace, Delimiter::Brace)
              | (Delimiter::Bracket, Delimiter::Bracket)
              | (Delimiter::None, Delimiter::None) => {}
              _ => return false,
            }

            let s1 = g1.stream().clone().into_iter();
            let mut s2 = g2.stream().clone().into_iter();

            for item1 in s1 {
              let item2 = match s2.next() {
                Some(item) => item,
                None => return false,
              };
              if TokenTreeHelper(&item1) != TokenTreeHelper(&item2) {
                return false;
              }
            }
            s2.next().is_none()
          }
          (&TokenTree::Punct(ref o1), &TokenTree::Punct(ref o2)) => {
            o1.as_char() == o2.as_char()
              && match (o1.spacing(), o2.spacing()) {
                (Spacing::Alone, Spacing::Alone) | (Spacing::Joint, Spacing::Joint) => true,
                _ => false,
              }
          }
          (&TokenTree::Literal(ref l1), &TokenTree::Literal(ref l2)) => {
            l1.to_string() == l2.to_string()
          }
          (&TokenTree::Ident(ref s1), &TokenTree::Ident(ref s2)) => s1 == s2,
          _ => false,
        }
      }
    }

    impl<'a> Hash for TokenTreeHelper<'a> {
      fn hash<H: Hasher>(&self, h: &mut H) {
        use proc_macro2::Spacing;

        match *self.0 {
          TokenTree::Group(ref g) => {
            0u8.hash(h);
            match g.delimiter() {
              Delimiter::Parenthesis => 0u8.hash(h),
              Delimiter::Brace => 1u8.hash(h),
              Delimiter::Bracket => 2u8.hash(h),
              Delimiter::None => 3u8.hash(h),
            }

            for item in g.stream().clone() {
              TokenTreeHelper(&item).hash(h);
            }
            0xffu8.hash(h); // terminator w/ a variant we don't normally hash
          }
          TokenTree::Punct(ref op) => {
            1u8.hash(h);
            op.as_char().hash(h);
            match op.spacing() {
              Spacing::Alone => 0u8.hash(h),
              Spacing::Joint => 1u8.hash(h),
            }
          }
          TokenTree::Literal(ref lit) => (2u8, lit.to_string()).hash(h),
          TokenTree::Ident(ref word) => (3u8, word).hash(h),
        }
      }
    }

    pub struct TokenStreamHelper<'a>(pub &'a TokenStream);

    impl<'a> PartialEq for TokenStreamHelper<'a> {
      fn eq(&self, other: &Self) -> bool {
        let left = self.0.clone().into_iter().collect::<Vec<_>>();
        let right = other.0.clone().into_iter().collect::<Vec<_>>();
        if left.len() != right.len() {
          return false;
        }
        for (a, b) in left.into_iter().zip(right) {
          if TokenTreeHelper(&a) != TokenTreeHelper(&b) {
            return false;
          }
        }
        true
      }
    }

    impl<'a> Hash for TokenStreamHelper<'a> {
      fn hash<H: Hasher>(&self, state: &mut H) {
        let tts = self.0.clone().into_iter().collect::<Vec<_>>();
        tts.len().hash(state);
        for tt in tts {
          TokenTreeHelper(&tt).hash(state);
        }
      }
    }
  }

  impl Parse for ItemFn {
    fn parse(input: ParseStream) -> Result<Self> {
      let outer_attrs = input.call(Attribute::parse_outer)?;
      let vis: Visibility = input.parse()?;
      let constness: Option<Token![const]> = input.parse()?;
      let asyncness: Option<Token![async]> = input.parse()?;
      let unsafety: Option<Token![unsafe]> = input.parse()?;
      let abi: Option<Abi> = input.parse()?;
      let fn_token: Token![fn] = input.parse()?;
      let ident: Ident = input.parse()?;
      let generics: Generics = input.parse()?;

      let content;
      let paren_token = parenthesized!(content in input);
      let inputs = content.parse_terminated(FnArg::parse)?;
      let variadic: Option<Token![...]> = match inputs.last() {
        Some(punctuated::Pair::End(&FnArg::Captured(ArgCaptured {
          ty: Type::Verbatim(TypeVerbatim { ref tts }),
          ..
        }))) => parse2(tts.clone()).ok(),
        _ => None,
      };

      let output: ReturnType = input.parse()?;
      let where_clause: Option<WhereClause> = input.parse()?;

      let content;
      let brace_token = braced!(content in input);
      let inner_attrs = content.call(Attribute::parse_inner)?;
      let stmts = content.call(Block::parse_within)?;

      Ok(ItemFn {
        attrs: private::attrs(outer_attrs, inner_attrs),
        vis: vis,
        constness: constness,
        asyncness: asyncness,
        unsafety: unsafety,
        abi: abi,
        ident: ident,
        decl: Box::new(FnDecl {
          fn_token: fn_token,
          paren_token: paren_token,
          inputs: inputs,
          output: output,
          variadic: variadic,
          generics: Generics {
            where_clause: where_clause,
            ..generics
          },
        }),
        block: Box::new(Block {
          brace_token: brace_token,
          stmts: stmts,
        }),
      })
    }
  }

  impl Parse for FnArg {
    fn parse(input: ParseStream) -> Result<Self> {
      if input.peek(Token![&]) {
        let ahead = input.fork();
        if ahead.call(arg_self_ref).is_ok() && !ahead.peek(Token![:]) {
          return input.call(arg_self_ref).map(FnArg::SelfRef);
        }
      }

      if input.peek(Token![mut]) || input.peek(Token![self]) {
        let ahead = input.fork();
        if ahead.call(arg_self).is_ok() && !ahead.peek(Token![:]) {
          return input.call(arg_self).map(FnArg::SelfValue);
        }
      }

      let ahead = input.fork();
      let err = match ahead.call(arg_captured) {
        Ok(_) => return input.call(arg_captured).map(FnArg::Captured),
        Err(err) => err,
      };

      let ahead = input.fork();
      if ahead.parse::<Type>().is_ok() {
        return input.parse().map(FnArg::Ignored);
      }

      Err(err)
    }
  }

  fn arg_self_ref(input: ParseStream) -> Result<ArgSelfRef> {
    Ok(ArgSelfRef {
      and_token: input.parse()?,
      lifetime: input.parse()?,
      mutability: input.parse()?,
      self_token: input.parse()?,
    })
  }

  fn arg_self(input: ParseStream) -> Result<ArgSelf> {
    Ok(ArgSelf {
      mutability: input.parse()?,
      self_token: input.parse()?,
    })
  }

  fn arg_captured(input: ParseStream) -> Result<ArgCaptured> {
    Ok(ArgCaptured {
      pat: input.parse()?,
      colon_token: input.parse()?,
      ty: match input.parse::<Token![...]>() {
        Ok(dot3) => {
          let args = vec![
            TokenTree::Punct(Punct::new('.', Spacing::Joint)),
            TokenTree::Punct(Punct::new('.', Spacing::Joint)),
            TokenTree::Punct(Punct::new('.', Spacing::Alone)),
          ];
          let tokens =
            TokenStream::from_iter(args.into_iter().zip(&dot3.spans).map(|(mut arg, span)| {
              arg.set_span(*span);
              arg
            }));
          Type::Verbatim(TypeVerbatim { tts: tokens })
        }
        Err(_) => input.parse()?,
      },
      dv: {
        if input.peek(Token![=]) {
          Some(input.parse()?)
        } else {
          None
        }
      },
    })
  }

  impl Parse for DefaultValue {
    fn parse(input: ParseStream) -> Result<Self> {
      Ok(DefaultValue {
        eq: input.parse()?,
        val: {
          let mut val = TokenStream::new();
          while !input.is_empty() && !input.peek(Token![,]) {
            val.extend(Some(input.parse::<TokenTree>()?))
          }
          val
        },
      })
    }
  }

  impl ToTokens for ItemFn {
    fn to_tokens(&self, tokens: &mut TokenStream) {
      tokens.append_all(self.attrs.outer());
      self.vis.to_tokens(tokens);
      self.constness.to_tokens(tokens);
      self.asyncness.to_tokens(tokens);
      self.unsafety.to_tokens(tokens);
      self.abi.to_tokens(tokens);
      NamedDecl(&self.decl, &self.ident).to_tokens(tokens);
      self.block.brace_token.surround(tokens, |tokens| {
        tokens.append_all(self.attrs.inner());
        tokens.append_all(&self.block.stmts);
      });
    }
  }

  struct NamedDecl<'a>(&'a FnDecl, &'a Ident);

  impl<'a> ToTokens for NamedDecl<'a> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
      self.0.fn_token.to_tokens(tokens);
      self.1.to_tokens(tokens);
      self.0.generics.to_tokens(tokens);
      self.0.paren_token.surround(tokens, |tokens| {
        self.0.inputs.to_tokens(tokens);
        if self.0.variadic.is_some() && !self.0.inputs.empty_or_trailing() {
          <Token![,]>::default().to_tokens(tokens);
        }
        self.0.variadic.to_tokens(tokens);
      });
      self.0.output.to_tokens(tokens);
      self.0.generics.where_clause.to_tokens(tokens);
    }
  }

  impl ToTokens for FnArg {
    fn to_tokens(&self, tokens: &mut TokenStream) {
      match self {
        SelfRef(ref _e) => _e.to_tokens(tokens),
        SelfValue(ref _e) => _e.to_tokens(tokens),
        Captured(ref _e) => _e.to_tokens(tokens),
        Inferred(ref _e) => _e.to_tokens(tokens),
        Ignored(ref _e) => _e.to_tokens(tokens),
      }
    }
  }

  impl ToTokens for ArgCaptured {
    fn to_tokens(&self, tokens: &mut TokenStream) {
      self.pat.to_tokens(tokens);
      self.colon_token.to_tokens(tokens);
      self.ty.to_tokens(tokens);
      self.dv.to_tokens(tokens);
    }
  }

  impl ToTokens for DefaultValue {
    fn to_tokens(&self, tokens: &mut TokenStream) {
      self.eq.to_tokens(tokens);
      self.val.to_tokens(tokens);
    }
  }

  mod private {
    use syn::Attribute;
    pub fn attrs(outer: Vec<Attribute>, inner: Vec<Attribute>) -> Vec<Attribute> {
      let mut attrs = outer;
      attrs.extend(inner);
      attrs
    }
  }

  mod attr {
    use std::iter;

    use syn::*;

    pub trait FilterAttrs<'a> {
      type Ret: Iterator<Item = &'a Attribute>;

      fn outer(self) -> Self::Ret;
      fn inner(self) -> Self::Ret;
    }

    impl<'a, T> FilterAttrs<'a> for T
    where
      T: IntoIterator<Item = &'a Attribute>,
    {
      type Ret = iter::Filter<T::IntoIter, fn(&&Attribute) -> bool>;

      fn outer(self) -> Self::Ret {
        #[cfg_attr(feature = "cargo-clippy", allow(trivially_copy_pass_by_ref))]
        fn is_outer(attr: &&Attribute) -> bool {
          match attr.style {
            AttrStyle::Outer => true,
            _ => false,
          }
        }
        self.into_iter().filter(is_outer)
      }

      fn inner(self) -> Self::Ret {
        #[cfg_attr(feature = "cargo-clippy", allow(trivially_copy_pass_by_ref))]
        fn is_inner(attr: &&Attribute) -> bool {
          match attr.style {
            AttrStyle::Inner(_) => true,
            _ => false,
          }
        }
        self.into_iter().filter(is_inner)
      }
    }
  }
}

mod argument {
  use proc_macro2::*;
  use quote::*;
  use syn::parse::*;
  use syn::punctuated::*;
  use syn::Token;
  use syn::{Expr, Pat, Type};

  use super::syn_default_parameter_patch::FnArg;

  #[derive(Clone)]
  pub struct InputArguments {
    pub args: Punctuated<InputArgument, Token![,]>,
  }
  #[derive(Clone)]
  pub enum InputArgument {
    Unnamed(UnnamedInputArgument),
    Named(NamedInputArgument),
  }
  #[derive(Clone)]
  pub struct UnnamedInputArgument {
    pub expr: Expr,
  }
  #[derive(Clone)]
  pub struct NamedInputArgument {
    pub pat: Pat,
    // should not empty at same time.
    pub ty: Option<TypeNotation>,
    pub val: Option<AssignedValue>,
  }

  #[derive(Clone)]
  pub struct TypeNotation {
    pub colon: Token![:],
    pub ty: Type,
  }
  #[derive(Clone)]
  pub struct AssignedValue {
    pub eq: Token![=],
    pub expr: Expr,
  }

  impl ToTokens for InputArguments {
    fn to_tokens(&self, tokens: &mut TokenStream) {
      self.args.to_tokens(tokens);
    }
  }

  impl ToTokens for InputArgument {
    fn to_tokens(&self, tokens: &mut TokenStream) {
      match self {
        InputArgument::Unnamed(uia) => uia.expr.to_tokens(tokens),
        InputArgument::Named(nia) => {
          let pat = &nia.pat;
          tokens.extend(quote!(#pat));
          let tn = &nia.ty;
          tokens.extend(quote!(#tn));
          let tn = &nia.val;
          tokens.extend(quote!(#tn));
        }
      }
    }
  }

  impl ToTokens for TypeNotation {
    fn to_tokens(&self, tokens: &mut TokenStream) {
      self.colon.to_tokens(tokens);
      self.ty.to_tokens(tokens);
    }
  }

  impl ToTokens for AssignedValue {
    fn to_tokens(&self, tokens: &mut TokenStream) {
      self.eq.to_tokens(tokens);
      self.expr.to_tokens(tokens);
    }
  }

  impl Parse for InputArguments {
    fn parse(input: ParseStream) -> Result<Self> {
      let mut args = Punctuated::new();
      loop {
        let test_parse = input.fork();
        let ia = if test_parse.parse::<Pat>().is_ok()
          && (test_parse.peek(Token![=]) || test_parse.peek(Token![:]))
        {
          let pat = input.parse()?;
          let ty = if input.peek(Token![:]) {
            let colon: Token![:] = input.parse()?;
            let ty = input.parse()?;
            Some(TypeNotation { colon, ty })
          } else {
            None
          };
          let val = if input.peek(Token![=]) {
            let eq: Token![=] = input.parse()?;
            let expr = input.parse()?;
            Some(AssignedValue { eq, expr })
          } else {
            None
          };
          InputArgument::Named(NamedInputArgument { pat, ty, val })
        } else {
          if input.is_empty() {
            break;
          }
          let expr = input.parse()?;
          InputArgument::Unnamed(UnnamedInputArgument { expr })
        };
        args.push(ia);

        if !input.peek(Token![,]) {
          break;
        }
        let punct: Token![,] = input.parse()?;
        args.push_punct(punct);
      }
      Ok(InputArguments { args })
    }
  }

  pub struct FnArgs {
    pub args: Punctuated<FnArg, Token![,]>,
  }

  impl ToTokens for FnArgs {
    fn to_tokens(&self, tokens: &mut TokenStream) {
      self.args.to_tokens(tokens);
    }
  }

  impl Parse for FnArgs {
    fn parse(input: ParseStream) -> Result<Self> {
      let args = input.parse_terminated(FnArg::parse)?;
      Ok(FnArgs { args })
    }
  }
}

mod enum_hack {
  use proc_macro2::*;
  use quote::*;
  use syn::parse::*;
  use syn::*;

  pub struct EnumHack {
    pub name: Ident,
    pub token_streams: Vec<TokenStream>,
  }

  pub fn wrap_in_enum_hack(dummy: &str, inner: Vec<TokenStream>) -> TokenStream {
    let dummy = Ident::new(dummy, Span::call_site());
    let eh = EnumHack {
      name: dummy,
      token_streams: inner,
    };
    let eh = eh.into_token_stream();
    quote!(
      #[derive(duang::ExpandEnumHack)]
      #eh
    )
  }

  impl ToTokens for EnumHack {
    fn to_tokens(&self, tokens: &mut TokenStream) {
      let name = &self.name;
      let size = Literal::usize_unsuffixed(self.token_streams.len());
      let contents = self.token_streams.iter().map(|ts| quote!(stringify! {#ts}));
      (quote! {
        enum #name {
          Value = (#(#contents),*, 0). #size,
        }
      })
      .to_tokens(tokens);
    }
  }

  impl Parse for EnumHack {
    fn parse(input: ParseStream) -> Result<Self> {
      input.parse::<Token![enum]>()?;
      let name = input.parse::<Ident>()?;

      let braces;
      braced!(braces in input);
      braces.parse::<Ident>()?;
      braces.parse::<Token![=]>()?;

      let parens;
      parenthesized!(parens in braces);
      let mut token_streams = Vec::new();
      while parens.peek(Ident) && parens.peek2(Token![!]) {
        parens.parse::<Ident>()?;
        parens.parse::<Token![!]>()?;

        let inner;
        braced!(inner in parens);
        token_streams.push(inner.parse::<TokenStream>()?);

        parens.parse::<Token![,]>()?;
      }

      parens.parse::<TokenTree>()?;
      braces.parse::<Token![.]>()?;
      braces.parse::<TokenTree>()?;
      braces.parse::<Token![,]>()?;

      Ok(EnumHack {
        name,
        token_streams,
      })
    }
  }
}

mod error {
  use proc_macro2::*;

  pub fn error(errmsg: &str, start: Span) -> TokenStream {
    error_range(errmsg, start, start)
  }

  pub fn error_range(errmsg: &str, start: Span, end: Span) -> TokenStream {
    let mut v = Vec::new();
    v.push(respan(Literal::string(&errmsg), Span::call_site()));
    let group = v.into_iter().collect();

    let mut r = Vec::<TokenTree>::new();
    r.push(respan(Ident::new("compile_error", start), start));
    r.push(respan(Punct::new('!', Spacing::Alone), Span::call_site()));
    r.push(respan(Group::new(Delimiter::Brace, group), end));

    r.into_iter().collect()
  }

  fn respan<T: Into<TokenTree>>(t: T, span: Span) -> TokenTree {
    let mut t = t.into();
    t.set_span(span);
    t
  }
}
