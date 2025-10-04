## 如何在 Vscode 中配置 Isabelle 环境

1. 在 [Isabelle](https://isabelle.in.tum.de/) 官网下载最新版本(2025 版) Isabelle 程序并安装。
2. 在 https://github.com/ponder-j/Isabelle-Vscode 下载 .vsix 插件文件(求 Star !)
3. 可以复制上面链接中 .vscode/isabelle.code-snippets 配置到你的 vscode 工作区或者全局 snippets
4. 在 vscode 中按 Ctrl + , 打开设置，右上角 Open Settings(JSON), 导入以下配置：

```json
	"isabelle.replacement": "none",
    "ISABELLE_OPTIONS": null,
    "editor.snippetSuggestions": "top",
    "files.associations": {
        "*.thy": "isabelle",
        "*.ML": "isabelle",
        "*.SML": "isabelle"
    },
    "[isabelle]": {
        "editor.fontFamily": "'Isabelle DejaVu Sans Mono', monospace",
    },
    "editor.unicodeHighlight.ambiguousCharacters": false,
```

5. 配置环境变量，以下是 Windows 电脑的配置示例(安装目录 `D:\Isabelle2025\Isabelle2025`)：

```
ISABELLE_HOME D:\Isabelle2025\Isabelle2025
CYGWIN_ROOT D:\Isabelle2025\Isabelle2025\contrib\cygwin
```

