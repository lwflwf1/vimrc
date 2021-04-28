" Description:   The path config of vim configuration
" Maintainer:    lwflwf1
" Website:       https://github.com/lwflwf1/vimrc
" Created Time:  2021-04-21 16:52:14
" Last Modified: 2021-04-28 16:25:49
" File:          config.vim
" License:       MIT

if has('nvim')
    let g:python3_host_prog = 'c:/disk_1/Miniconda/envs/study/python.exe'
    let g:python_host_prog = 'c:/disk_1/Miniconda/envs/study/python.exe'
    let g:data_dir = stdpath('data').'/'
else
    let g:data_dir = '~/.vim/'
endif

" let g:perl_host_prog = 'C:/disk_1/Perl/StrawberryPerl5.30/perl/bin/perl5.30.1.exe'
" let g:python_highlight_all = 1

if has('win32') || has('win64')
    let g:is_windows = 1
else
    let g:is_windows = 0
endif

let g:dein_dir = 'C:/Users/79941/AppData/Local/nvim-data/dein'
set rtp+=C:/disk_1/fzf
