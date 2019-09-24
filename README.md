# AutBound: Code generator for abstract syntax trees

## Usage

The executable can be used from the command line with the following arguments:

```
autbound SOURCE_FILE OUTPUT_LANGUAGE VARIABLE_TYPE OUTPUT_NAME
```

For example, if we want to generate a Haskell module called `FCoBase` from the FCo specification, using string-based variables, we would issue the command:

```
autbound "Specifications/FCo.txt" Haskell String FCoBase
```

This will generate the file `FCoBase.hs` in the current directory.

The following options are currently available:
- `OUTPUT_LANGUAGE`: `Haskell`, `OCaml`
- `VARIABLE_TYPE`: `DeBruijn`, `String`

## Language descriptions

Language descriptions are simple text files. They consist of four different parts:

- Import declarations
- Namespace declarations
- Sort declarations
- Native code

None of these sections are mandatory.

For examples of language descriptions, see the `Specifications` directory.
