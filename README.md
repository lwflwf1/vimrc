# Vim(NeoVim)-Configuration

Vim(Neovim) configuration files

## Feature

- code completion and snippets
- definition, reference and project file jumping
- code linting
- run code and tasks easily and asynchonously
- code refactor for python
- markdown preview and snippets
- powerful searching capability for files, mru files, functions, classes, tags and any text
- powerful replacing capability
- git integration
- file explorer integration
- multiple cursor support
- easy-to-use ternimal integration
- chinese vim doc
- english translation

## Structure

This Vim(Neovim) configuration contains 6 files:

1. init.vim: the entry of all .vim files
2. basic.vim: the basic settings
3. keymap.vim: plugin indenpendent keymaps
4. plugins.vim: all plugins, related keymaps and settings
5. config.vim: executable path
6. coc-settings.json: settings of coc.nvim plugin
7. ginit.vim: settings of nvim-qt

Besides these files, Ultisnips directory contains all snippet files

## Requirement

1. `vim(neovim)`

    For the best experience, install the latest vim(neovim)

2. `vim configuration`

    `--enable-pythoninterp`, `--enable-python3interp`

3. `python`

    Plugin `semshi` and `LeaderF` requires python3

    If you are using neovim, install `pynvim`

    ```bash
    pip install --user --upgrade pynvim
    ```

4. `node.js`

    Plugin `coc.nvim` requires [node.js >= 10.12](https://nodejs.org/zh-cn/)

    Install the latest node.js

    ```bash
    curl -sL install-node.now.sh | sh
    ```

5. `universal-ctags`

    If you want to use tags, install [universal-ctags](https://github.com/universal-ctags/ctags)

6. `git`

    Install the latest [git](https://git-scm.com/)

7. `fzf`

    Some plugins can work with fzf. If you want to use this feature, install the latest [fzf](https://github.com/junegunn/fzf)

8. `ripgrep`

    Some plugins can work with ripgrep. If you want to use this feature, install the latest [ripgrep](https://github.com/BurntSushi/ripgrep)

9. `nerd font`

    Some plugins need nerd font to display icons. If you want to use this feature, install a [nerd font](https://github.com/ryanoasis/nerd-fonts)

## Installation

First, use `:version` to check the version of Vim(Neovim), because some plugins will not be installed if the verison is not satisfied.

Neovim >= 0.4.2 or Vim >= 8.2.0750 is the best.

Second, install [vim-plug](https://github.com/junegunn/vim-plug).

**Vim**

Unix

```bash
curl -fLo ~/.vim/autoload/plug.vim --create-dirs \
    https://raw.githubusercontent.com/junegunn/vim-plug/master/plug.vim
```

Windows(PowerShell)

```ps1
iwr -useb https://raw.githubusercontent.com/junegunn/vim-plug/master/plug.vim |`
    ni $HOME/vimfiles/autoload/plug.vim -Force
```

**Neovim**

Unix, Linux

```bash
sh -c 'curl -fLo "${XDG_DATA_HOME:-$HOME/.local/share}"/nvim/site/autoload/plug.vim --create-dirs \
       https://raw.githubusercontent.com/junegunn/vim-plug/master/plug.vim'
```

Windows(PowerShell)

```ps1
iwr -useb https://raw.githubusercontent.com/junegunn/vim-plug/master/plug.vim |`
    ni "$(@($env:XDG_DATA_HOME, $env:LOCALAPPDATA)[$null -eq $env:XDG_DATA_HOME])/nvim-data/site/autoload/plug.vim" -Force
```

Second, git clone this repository, and put files into your path.

Third, open Vim(Neovim) and execute `:PlugInstall`.

Last, configure `config.vim`.

## Keymaps

There are 2 types of keymaps:

- the basic keymaps which are not related to plugins
- the keymaps related to plugins

### Basic Keymaps

| **keymaps**   | **mode**         | **description**                                                                           |
|---------------|------------------|-------------------------------------------------------------------------------------------|
| `<`           | normal           | left indent                                                                               |
| `>`           | normal           | right indent                                                                              |
| `H`           | normal           | move cursor to the first character of the line                                            |
| `L`           | normal           | move cursor to the end of the line                                                        |
| `Y`           | normal           | yank from the cursor to the end of the line `y$`                                          |
| `<backspace>` | normal           | no highlight search                                                                       |
| `<m-h>`       | normal           | move cursor to the left window                                                            |
| `<m-j>`       | normal           | move cursor to the below window                                                           |
| `<m-k>`       | normal           | move cursor to the up window                                                              |
| `<m-l>`       | normal           | move cursor to the right window                                                           |
| `<c-h>`       | normal           | move to the left tab if there is more than one tab else move to the left buffer           |
| `<c-l>`       | normal           | move to the right tab if there is more than one tab else move to the right buffer         |
| `-`           | normal           | move to the previous tab                                                                  |
| `=`           | normal           | move to the next tab                                                                      |
| `tu`          | normal           | create a new tab                                                                          |
| `<m-q>`       | normal           | delete current buffer                                                                     |
| `sh`          | normal           | split vertically and set the cursor to the left window                                    |
| `sl`          | normal           | split vertically and set the cursor to the right window                                   |
| `sj`          | normal           | split horizontally and set the cursor to the below window                                 |
| `sk`          | normal           | split horizontally and set the cursor to the up window                                    |
| `<up>`        | normal           | `resize +5`                                                                               |
| `<down>`      | normal           | `resize -5`                                                                               |
| `<left>`      | normal           | `vertical resize -5`                                                                      |
| `<right>`     | normal           | `vertical resize +5`                                                                      |
| `<leader>"`   | normal           | enclose the word under the cursor with `""`                                               |
| `<leader>'`   | normal           | enclose the word under the cursor with `''`                                               |
| `<leader>(`   | normal           | enclose the word under the cursor with `()`                                               |
| `<leader>[`   | normal           | enclose the word under the cursor with `[]`                                               |
| `<leader>{`   | normal           | enclose the word under the cursor with `{}`                                               |
| `<leader>rc`  | normal           | open vimrc file (this shortcut is valid only if the environment variable $MYVIMRC exists) |
| `src`         | normal           | source vimrc (this shortcut is valid only if the environment variable $MYVIMRC exists)    |
| `<leader>/`   | normal           | search in **very magic** mode                                                             |
| `jj`          | insert           | return to normal mode                                                                     |
| `<c-a>`       | insert           | move cursor to the beginning of the line                                                  |
| `<c-e>`       | insert           | move cursor to the end of the line                                                        |
| `<c-d>`       | insert           | delete the character after the cursor                                                     |
| `<c-h>`       | insert           | move cursor left                                                                          |
| `<c-l>`       | insert           | move cursor right                                                                         |
| `<m-h>`       | insert           | move cursor one word before                                                               |
| `<m-l>`       | insert           | move cursor one word after                                                                |
| `<m-o>`       | insert           | start a new line below                                                                    |
| `<m-O>`       | insert           | start a new line up                                                                       |
| `<c-k>`       | insert           | change the word under the cursor to uppercase                                             |
| `<esc>`       | ternimal insert  | return to ternimal normal mode                                                            |
| `m-i`         | normal or insert | find the placeholder `<++>` and insert                                                    |
| `u`           | visual           | change the selected text to lowercase                                                     |
| `U`           | visual           | change the selected text to uppercase                                                     |

keymaps only for markdown

| **keymaps**    | **mode** | **description**  |
|----------------|----------|------------------|
| `<m-(number)>` | insert   | number:1-6 title |
| `<m-b>`        | insert   | bold             |
| ``<m-`>``      | insert   | inline code      |
| `<m-c>`        | insert   | code             |
| `<m-p>`        | insert   | picture          |
| `<m-u>`        | insert   | url              |

## TODO

keymaps related to plugins

install vim-plug automatically

code debugging

move functions to a seperate .vim file

chinese version of this README.md

toc

more detailed comment in .vim files
