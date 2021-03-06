" Description:   The path config of vim configuration
" Maintainer:    lwflwf1
" Website:       https://github.com/lwflwf1/vimrc
" Created Time:  2021-04-21 16:52:14
" Last Modified: 2021-08-08 13:52:13
" File:          config.vim
" License:       MIT

if has('nvim')
    let g:data_dir = stdpath('data').'/'
    let g:python3_host_prog = 'c:/disk_1/Miniconda/envs/neovim/python.exe'
    let g:python_host_prog = 'c:/disk_1/Miniconda/envs/neovim/python.exe'
    let g:perl_host_prog = 'c:/disk_1/Perl/StrawberryPerl5.30/perl/bin/perl5.30.1.exe'
    let g:node_host_prog = 'c:/Users/79941/AppData/Roaming/npm/node_modules/neovim/bin/cli.js'
else
    let g:data_dir = $HOME.'/.vim/'
endif

if has('win32') || has('win64')
    let g:os = 'windows'
elseif has('unix')
    let g:os = 'unix'
else
    let g:os = 'macos'
endif

let g:dein_dir = 'C:/Users/79941/AppData/Local/nvim-data/dein'

" this saves startup time
if g:os ==# 'windows'
    let g:clipboard = {
        \ 'name': 'win32yank',
        \ 'copy': {
        \ '+': 'win32yank.exe -i --crlf',
        \ '*': 'win32yank.exe -i --crlf',
        \ },
        \ 'paste': {
        \ '+': 'win32yank.exe -o --lf',
        \ '*': 'win32yank.exe -o --lf',
        \ },
        \ 'cache_enabled': 0,
        \ }
elseif g:os ==# 'macos'
    let g:clipboard = {
        \ 'name': 'pbcopy',
        \ 'copy': {
        \    '+': 'pbcopy',
        \    '*': 'pbcopy',
        \  },
        \ 'paste': {
        \    '+': 'pbpaste',
        \    '*': 'pbpaste',
        \ },
        \ 'cache_enabled': 0,
        \ }
endif
