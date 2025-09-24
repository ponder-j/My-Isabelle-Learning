# Isabelle Syntax Highlighter

A Visual Studio Code extension that provides comprehensive syntax highlighting for Isabelle theorem prover files (.thy).

## Features

- **Comprehensive syntax highlighting** for Isabelle/HOL theory files
- **Support for Isabelle symbols** (\\<forall>, \\<exists>, \\<Rightarrow>, etc.)
- **Keyword highlighting** for proof commands, definitions, and declarations
- **Comment support** for both line comments (--) and block comments ((* *))
- **Bracket matching** including Isabelle-specific brackets (\\<lparr>...\\<rparr>, \\<lbrakk>...\\<rbrakk>)
- **Type annotation highlighting**
- **Auto-indentation** for proof blocks

## Supported Elements

### Keywords
- **Theory structure**: `theory`, `imports`, `begin`, `end`
- **Definitions**: `definition`, `fun`, `function`, `primrec`
- **Types**: `datatype`, `typedef`, `type_synonym`, `record`
- **Proof commands**: `lemma`, `theorem`, `proof`, `qed`, `by`, `apply`
- **Locale system**: `locale`, `context`, `interpretation`
- **Class system**: `class`, `instance`, `instantiation`

### Isabelle Symbols
- **Logical**: \\<and>, \\<or>, \\<not>, \\<forall>, \\<exists>
- **Arrows**: \\<Rightarrow>, \\<longrightarrow>, \\<Leftrightarrow>
- **Set operations**: \\<in>, \\<union>, \\<inter>, \\<subset>
- **Mathematical**: \\<le>, \\<ge>, \\<times>, \\<div>
- **Lambda**: \\<lambda>, \\<Lambda>

### Comments
```isabelle
(* Block comment *)
-- Line comment
```

## Installation

### From VSIX file
1. Download the `.vsix` file
2. Open VS Code
3. Press `Ctrl+Shift+P` (Windows/Linux) or `Cmd+Shift+P` (macOS)
4. Type "Extensions: Install from VSIX..."
5. Select the downloaded `.vsix` file

### Manual Installation
1. Clone this repository
2. Copy the entire folder to your VS Code extensions directory:
   - **Windows**: `%USERPROFILE%\\.vscode\\extensions\\`
   - **macOS**: `~/.vscode/extensions/`
   - **Linux**: `~/.vscode/extensions/`
3. Reload VS Code

## Usage

Once installed, the extension will automatically activate when you open `.thy` files. The syntax highlighting will be applied immediately.

## Example

```isabelle
theory Example
  imports Main
begin

definition factorial :: "nat ⇒ nat"
  where "factorial n ≡ (if n = 0 then 1 else n * factorial (n - 1))"

lemma factorial_positive: "factorial n > 0"
proof (induction n)
  case 0
  show ?case by (simp add: factorial_def)
next
  case (Suc n)
  show ?case by (simp add: factorial_def Suc.IH)
qed

end
```

## Contributing

If you find any issues or have suggestions for improvements, please feel free to create an issue or submit a pull request.

## License

This project is licensed under the MIT License.