# histutils

Import, export or merge zsh or fish history files.

## Usage

Merge multiple history files into a single file.

```
$ histutils --format zsh ~/.zsh_sessions/*.history
```

Migrate formats.

```
$ cat ~/.zsh_history | histutils --format fish
$ cat ~/.local/share/fish/fish_history | histutils --format zsh
```
