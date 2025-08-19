# histutils

Import, export or merge zsh extended or fish history files.

## Usage

Merge multiple history files into a single file.

```
$ histutils --output-format zsh-extended ~/.zsh_sessions/*.history
```

Migrate formats.

```
$ cat ~/.zsh_history | histutils --output-format fish
$ cat ~/.local/share/fish/fish_history | histutils --output-format zsh-extended
```

Count entries in a history file.

```
$ histutils --count ~/.zsh_history
```
