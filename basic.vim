" Description:   The basic settings of vim configuration
" Maintainer:    lwflwf1
" Website:       https://github.com/lwflwf1/vimrc
" Created Time:  2021-04-21 16:49:06
" Last Modified: 2021-07-05 00:52:28
" File:          basic.vim
" License:       MIT

set nocompatible
syntax on
syntax enable
filetype plugin indent on
set diffopt=vertical,filler,internal,context:4
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
" set guifont=Inconsolata\ NF:h16
set guifont=JetBrainsMono\ NF:h15
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
set clipboard=unnamedplus
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
set undofile
set nobackup
set noswapfile
set noshowmode
set confirm
set conceallevel=2
set concealcursor="nc"
set backspace=indent,eol,start
set nrformats=bin,hex,alpha
set sessionoptions-=blank
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
if g:os ==# 'windows'
    set winaltkeys=no " Don't use ALT key for menus in Windows, so ALT can be used for mapping
endif
" winheight is not compatible with coc.nvim, must not set for now
" set winheight=10
" set winminheight=2
if has('nvim')
    set fillchars=eob:\ 
endif
if executable('rg')
    set grepformat=%f:%l:%m
    let &grepprg = 'rg --vimgrep' . (&smartcase ? ' --smart-case' : '')
endif
if has('nvim')
    set inccommand=nosplit
    set signcolumn=yes:2
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

if has('nvim') == 0 && has('gui_running') == 0

    function! s:metacode(key)
        exec "set <M-".a:key.">=\e".a:key
    endfunc

    for i in range(10)
        call s:metacode(nr2char(char2nr('0') + i))
    endfor
    for i in range(26)
        call s:metacode(nr2char(char2nr('a') + i))
        call s:metacode(nr2char(char2nr('A') + i))
    endfor
    for c in [',', '.', '/', ';', '{', '}']
        call s:metacode(c)
    endfor
    for c in ['?', ':', '-', '_', '+', '=', "'"]
        call s:metacode(c)
    endfor

    function! s:key_escape(name, code)
        exec "set ".a:name."=\e".a:code
    endfunc

    call s:key_escape('<F1>', 'OP')
    call s:key_escape('<F2>', 'OQ')
    call s:key_escape('<F3>', 'OR')
    call s:key_escape('<F4>', 'OS')
    call s:key_escape('<S-F1>', '[1;2P')
    call s:key_escape('<S-F2>', '[1;2Q')
    call s:key_escape('<S-F3>', '[1;2R')
    call s:key_escape('<S-F4>', '[1;2S')
    call s:key_escape('<S-F5>', '[15;2~')
    call s:key_escape('<S-F6>', '[17;2~')
    call s:key_escape('<S-F7>', '[18;2~')
    call s:key_escape('<S-F8>', '[19;2~')
    call s:key_escape('<S-F9>', '[20;2~')
    call s:key_escape('<S-F10>', '[21;2~')
    call s:key_escape('<S-F11>', '[23;2~')
    call s:key_escape('<S-F12>', '[24;2~')

endif

"----------------------------------------------------------------------
" 防止tmux下vim的背景色显示异常
" Refer: http://sunaku.github.io/vim-256color-bce.html
"----------------------------------------------------------------------
if &term =~ '256color' && $TMUX != ''
    " disable Background Color Erase (BCE) so that color schemes
    " render properly when inside 256-color tmux and GNU screen.
    " see also http://snk.tuxfamily.org/log/vim-256color-bce.html
    set t_ut=
endif

if has('nvim')
    set guicursor=
elseif (!has('gui_running')) && has('terminal') && has('patch-8.0.1200')
    let g:termcap_guicursor = &guicursor
    let g:termcap_t_RS = &t_RS
    let g:termcap_t_SH = &t_SH
    set guicursor=
    set t_RS=
    set t_SH=
endif

set suffixes=.bak,~,.o,.h,.info,.swp,.obj,.pyc,.pyo,.egg-info,.class

set wildignore=*.o,*.obj,*~,*.exe,*.a,*.pdb,*.lib "stuff to ignore when tab completing
set wildignore+=*.so,*.dll,*.swp,*.egg,*.jar,*.class,*.pyc,*.pyo,*.bin,*.dex
set wildignore+=*.zip,*.7z,*.rar,*.gz,*.tar,*.gzip,*.bz2,*.tgz,*.xz    " MacOSX/Linux
set wildignore+=*DS_Store*,*.ipch
set wildignore+=*.gem
set wildignore+=*.png,*.jpg,*.gif,*.bmp,*.tga,*.pcx,*.ppm,*.img,*.iso
set wildignore+=*.so,*.swp,*.zip,*/.Trash/**,*.pdf,*.dmg,*/.rbenv/**
set wildignore+=*/.nx/**,*.app,*.git,.git
set wildignore+=*.wav,*.mp3,*.ogg,*.pcm
set wildignore+=*.mht,*.suo,*.sdf,*.jnlp
set wildignore+=*.chm,*.epub,*.pdf,*.mobi,*.ttf
set wildignore+=*.mp4,*.avi,*.flv,*.mov,*.mkv,*.swf,*.swc
set wildignore+=*.ppt,*.pptx,*.docx,*.xlt,*.xls,*.xlsx,*.odt,*.wps
set wildignore+=*.msi,*.crx,*.deb,*.vfd,*.apk,*.ipa,*.bin,*.msu
set wildignore+=*.gba,*.sfc,*.078,*.nds,*.smd,*.smc
set wildignore+=*.linux2,*.win32,*.darwin,*.freebsd,*.linux,*.android

" set ambiwidth=double
" set lazyredraw
" set showmatch
" set matchtime=1
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


" 定位到退出位置并移动到屏幕中央
augroup return_exit_positon
  autocmd!
  autocmd BufReadPost * if line("'\"") > 1 && line("'\"") <= line("$") | execute "normal! g'\"" | endif | normal! zvzz
augroup END

augroup update_last_modified_on_write
  autocmd!
  autocmd BufWritePre * call functions#UpdateLastModified()
augroup END

augroup nolist_group
    autocmd!
    autocmd FileType help,git,gitcommit setlocal nolist | setlocal nonumber | setlocal norelativenumber | setlocal signcolumn=no
augroup END

augroup q_for_quit_on_helpfile_group
    autocmd!
    autocmd FileType help nnoremap <silent> <buffer> q :bwipeout<cr>
augroup END
