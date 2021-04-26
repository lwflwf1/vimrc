" Description:   The entrance of all vim configuration files
" Maintainer:    lwflwf1
" Website:       https://github.com/lwflwf1/
" Created Time:  2021-04-21 17:13:59
" Last Modified: 2021-04-26 01:19:42
" File:          init.vim
" License:       MIT

" if empty(glob('~/.config/nvim/autoload/plug.vim'))
"         silent !curl -fLo ~/.config/nvim/autoload/plug.vim --create-dirs
"                     \ https://raw.githubusercontent.com/junegunn/vim-plug/master/plug.vim
"     autocmd VimEnter * PlugInstall --sync | source $MYVIMRC
" endif

" get the directory of this init.vim file

let g:vimrc = resolve(expand('<sfile>:p'))
let g:vimrc_directory = fnamemodify(g:vimrc, ':h')

" define a command for loadscript
command! -nargs=1 LoadScript exec 'source '.g:vimrc_directory.'/'.'<args>'

LoadScript config.vim
LoadScript basic.vim
LoadScript keymap.vim
LoadScript plugin.vim

delcommand LoadScript
