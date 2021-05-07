" Description:   The entrance of all vim configuration files
" Maintainer:    lwflwf1
" Website:       https://github.com/lwflwf1/vimrc
" Created Time:  2021-04-21 17:13:59
" Last Modified: 2021-05-07 10:27:45
" File:          init.vim
" License:       MIT

let g:vimrc = resolve(expand('<sfile>:p'))
let g:vimrc_directory = fnamemodify(g:vimrc, ':h')

command! -nargs=1 LoadScript exec 'source '.g:vimrc_directory.'/'.'<args>'

LoadScript config.vim
LoadScript basic.vim
LoadScript keymap.vim
LoadScript plugin.vim

delcommand LoadScript
