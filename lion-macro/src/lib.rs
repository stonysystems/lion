use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, ItemFn, Token};
use syn::parse::{Parse, ParseStream};

struct MainArgs {
  _flavor: Option<String>,
  _worker_threads: Option<usize>,
}

impl Parse for MainArgs {
  fn parse(input: ParseStream) -> syn::Result<Self> {
    let mut flavor = None;
    let mut worker_threads = None;

    while !input.is_empty() {
      let ident: syn::Ident = input.parse()?;
      let _: Token![=] = input.parse()?;

      match ident.to_string().as_str() {
        "flavor" => {
          let lit: syn::LitStr = input.parse()?;
          flavor = Some(lit.value());
        }
        "worker_threads" => {
          let lit: syn::LitInt = input.parse()?;
          worker_threads = Some(lit.base10_parse()?);
        }
        other => {
          return Err(syn::Error::new_spanned(
            &ident,
            format!("unknown attribute `{other}`"),
          ));
        }
      }

      if !input.is_empty() {
        let _: Token![,] = input.parse()?;
      }
    }

    Ok(MainArgs {
      _flavor: flavor,
      _worker_threads: worker_threads,
    })
  }
}

#[proc_macro_attribute]
pub fn main(attr: TokenStream, item: TokenStream) -> TokenStream {
  let _args = parse_macro_input!(attr as MainArgs);
  let input = parse_macro_input!(item as ItemFn);

  let attrs = &input.attrs;
  let vis = &input.vis;
  let sig = &input.sig;
  let body = &input.block;

  if sig.asyncness.is_none() {
    return syn::Error::new_spanned(
      &sig.fn_token,
      "#[lion::main] can only be applied to async functions",
    )
    .to_compile_error()
    .into();
  }

  let name = &sig.ident;
  let inputs = &sig.inputs;
  let output = &sig.output;
  let generics = &sig.generics;

  let result = quote! {
    #(#attrs)*
    #vis fn #name #generics (#inputs) #output {
      ::lion::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap()
        .block_on(async #body)
    }
  };

  result.into()
}

#[proc_macro_attribute]
pub fn test(attr: TokenStream, item: TokenStream) -> TokenStream {
  let _args = parse_macro_input!(attr as MainArgs);
  let input = parse_macro_input!(item as ItemFn);

  let attrs = &input.attrs;
  let vis = &input.vis;
  let sig = &input.sig;
  let body = &input.block;

  if sig.asyncness.is_none() {
    return syn::Error::new_spanned(
      &sig.fn_token,
      "#[lion::test] can only be applied to async functions",
    )
    .to_compile_error()
    .into();
  }

  let name = &sig.ident;
  let inputs = &sig.inputs;
  let output = &sig.output;
  let generics = &sig.generics;

  let result = quote! {
    #[::core::prelude::v1::test]
    #(#attrs)*
    #vis fn #name #generics (#inputs) #output {
      ::lion::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap()
        .block_on(async #body)
    }
  };

  result.into()
}
