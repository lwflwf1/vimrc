" Description:   The basic settings of vim configuration
" Maintainer:    lwflwf1
" Website:       https://github.com/lwflwf1/vimrc
" Created Time:  2021-04-21 16:49:06
" Last Modified: 2021-04-26 19:55:11
" File:          basic.vim
" License:       MIT

set nocompatible
syntax on
syntax enable
set fileformat=unix
set termguicolors
set autoindent
set smartindent
set mouse=a
set number
set relativenumber
set wildmenu
set showcmd
set hlsearch
set incsearch
set wrapscan
set ignorecase
set smartcase
set infercase
set guifont=Inconsolata\ NF:h16
" set guifont=JetBrainsMono\ NF:h14
set linespace=5
set encoding=utf-8
scriptencoding utf-8
set fileencodings=utf-8,gbk,ucs-bom
set expandtab
set smarttab
set tabstop=4
set shiftwidth=4
set softtabstop=4
set shiftround
set list
set listchars=tab:»\ ,trail:·,extends:→,precedes:←
set foldmethod=indent "manual indent expr syntax diff marker. enter zf<text object> to create a fold
set foldenable
set foldlevelstart=99
set laststatus=2
set autochdir
set wrap
set noruler
set linebreak
set clipboard+=unnamedplus
set scrolloff=3 " make the cursor always 5 lines from the top or bottom
set sidescrolloff=5
set completeopt=menu,menuone,noselect
set complete=.,k,w,b,t
set pumheight=15
set shortmess+=c
set hidden
set updatetime=100
set showtabline=2
set autoread
set noerrorbells
set visualbell
set undofile
set nobackup
set noswapfile
set winaltkeys=no " Don't use ALT key for menus in Windows, so ALT can be used for mapping
set noshowmode
set confirm
set conceallevel=2
set concealcursor="nc"
set backspace=indent,eol,start
set nrformats=bin,hex,alpha
set sessionoptions-=blank
set sessionoptions-=help
set sessionoptions-=options
set sessionoptions+=unix
set timeout
set ttimeout
set timeoutlen=700
set ttimeoutlen=50
set virtualedit=block
set synmaxcol=2500
set formatoptions-=o
set formatoptions+=j
set textwidth=80
set nostartofline
set splitbelow
set splitright
set switchbuf=useopen
set matchpairs+=<:>
set winwidth=30
set winminwidth=10
set winheight=10
set winminheight=2
set rtp+=C:/disk_1/fzf
" set fillchars=eob:\ 
let &fillchars='eob: '
" set rtp+=C:/disk_1/Microsoft\ VS\ Code/resources/app/node_modules.asar.unpacked/vscode-ripgrep/bin/rg.exe
if executable('rg')
    set grepformat=%f:%l:%m
    let &grepprg = 'rg --vimgrep' . (&smartcase ? ' --smart-case' : '')
endif
if has('nvim')
    set inccommand=nosplit
    set signcolumn=auto:2
else
    set signcolumn=yes
endif

if has('gui_running')
    set guioptions-=m " Hide menu bar.
    set guioptions-=T " Hide toolbar
    set guioptions-=L " Hide left-hand scrollbar
    set guioptions-=r " Hide right-hand scrollbar
    set guioptions-=b " Hide bottom scrollbar
    set showtabline=0 " Hide tabline
    set guioptions-=e " Hide tab
endif
filetype plugin indent on
set runtimepath+=C:/disk_2/vim-session-manager
source c:/disk_2/vim-session-manager/plugin/vim-session-manager.vim
source c:/disk_2/vim-smart-hlsearch/plugin/vim-smart-hlsearch.vim

" set ambiwidth=double
" set lazyredraw
" set showmatch
" set matchtime=1
" set t_Co=256
" set shell=powershell.exe
" set virtualedit=block,onemore
" set cindent
" set cinoptions=g0,:0,N-s,(0
" set langmenu=zh_CN.UTF-8
" set path+=**
" set wildmode=longest:full
" if has('nvim') && ! has('win32') && ! has('win64')
"     set shada=!,'300,<50,@100,s10,h
" else
"     set viminfo='300,<10,@50,h,n$DATA_PATH/viminfo
" endif
" set diffopt=filler,iwhite
" if has('patch-8.1.0360') || has('nvim-0.4')
"     set diffopt+=internal,algorithm:patience
" endif
" set fillchars+=vert:\|
" set title
" " Title length.
" set titlelen=95
" " Title string.
" let &g:titlestring="
"       \ %{expand('%:p:~:.')}%(%m%r%w%)
      " \ %<\[%{fnamemodify(getcwd(), ':~')}\] - Neovim"

let s:backup_dir = g:data_dir.'backup'
let s:undo_dir   = g:data_dir.'undo'
let s:swap_dir   = g:data_dir.'swap'
let s:view_dir   = g:data_dir.'view'
let s:dir_list   = [s:swap_dir, s:undo_dir, s:backup_dir, s:view_dir]
for dir in s:dir_list
    if !isdirectory(dir)
        silent call mkdir(dir, 'p')
    endif
endfor
let &undodir   = s:undo_dir
let &directory = s:swap_dir
let &backupdir = s:backup_dir
let &viewdir   = s:view_dir
unlet s:backup_dir
unlet s:undo_dir
unlet s:swap_dir
unlet s:view_dir
unlet s:dir_list

if !exists("g:plugs")
    " mode, buffer number, file path, preview window flag,
    " modified flag, read only flag
    let s:mode_dict = {
        \ 'n'  : 'NORMAL',
        \ 'c'  : 'COMMAND',
        \ 'i'  : 'INSERT',
        \ 't'  : 'INSERT',
        \ 'v'  : 'VISUAL',
        \ 'V'  : 'VLINE',
        \ '' : 'VBLOCK',
        \ 's'  : 'SELECT',
        \ 'S'  : 'SELECT',
        \ '' : 'SELECT',
        \ 'r'  : 'REPLACE',
        \ 'R'  : 'REPLACE',
      \ }
    set statusline=\ %{functions#GetMode()}\ \|\ [%n]\ %F\ %w\ %m\ %r
    if exists('g:loaded_vim_session_manager')
        set statusline+=\ %{SessionStatusLine()}
    endif
    set statusline+=%=
    " filetype, percentage, line number, total line numbers, column number
    set statusline+=%y\ %p%%\ ☰\ %l/%L\ :%c
endif

execute "nohlsearch"

"if (empty($TMUX))
"    if (has("nvim"))
"        "For Neovim 0.1.3 and 0.1.4 < https://github.com/neovim/neovim/pull/2198 >
"        let $NVIM_TUI_ENABLE_TRUE_COLOR=1
"    endif
"    "For Neovim > 0.1.5 and Vim > patch 7.4.1799 < https://github.com/vim/vim/commit/61be73bb0f965a895bfb064ea3e55476ac175162 >
"    "Based on Vim patch 7.4.1770 (`guicolors` option) < https://github.com/vim/vim/commit/8a633e3427b47286869aa4b96f2bfc1fe65b25cd >
"    " < https://github.com/neovim/neovim/wiki/Following-HEAD#20160511 >
"    if (has("termguicolors"))
"        set termguicolors
"    endif
"endif

let g:netrw_liststyle = 3
let g:netrw_browse_split = 3

let g:match_words = '\<if\>:\<endif\>:\<else\>,'
\ . '\<while\>:\<continue\>,'
\ . '\<begin\>:\<end\>,'
\ . '\<module\>:\<endmodule\>,'
\ . '\<class\>:\<endclass\>,'
\ . '\<program\>:\<endprogram\>,'
\ . '\<clocking\>:\<endclocking\>,'
\ . '\<property\>:\<endproperty\>,'
\ . '\<sequence\>:\<endsequence\>,'
\ . '\<package\>:\<endpackage\>,'
\ . '\<covergroup\>:\<endgroup\>,'
\ . '\<primitive\>:\<endprimitive\>,'
\ . '\<specify\>:\<endspecify\>,'
\ . '\<generate\>:\<endgenerate\>,'
\ . '\<interface\>:\<endinterface\>,'
\ . '\<function\>:\<endfunction\>,'
\ . '\<task\>:\<endtask\>,'
\ . '\<case\>\|\<casex\>\|\<casez\>:\<endcase\>,'
\ . '\<fork\>:\<join\>\|\<join_any\>\|\<join_none\>,'
\ . '`ifdef\>:`else\>:`endif\>,'
\ . '\<generate\>:\<endgenerate\>'

" 定位到退出位置并移动到屏幕中央
augroup return_exit_positon
  autocmd!
  autocmd BufReadPost * if line("'\"") > 1 && line("'\"") <= line("$") | execute "normal! g'\"" | endif | normal! zvzz
augroup END

augroup update_last_modified_on_write
  autocmd!
  autocmd BufWritePre * call functions#UpdateLastModified()
augroup END
