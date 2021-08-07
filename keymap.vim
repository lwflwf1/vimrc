" Description:   The plugin independent keymaps of vim configuration
" Maintainer:    lwflwf1
" Website:       https://github.com/lwflwf1/vimrc
" Created Time:  2021-04-21 16:54:10
" Last Modified: 2021-08-07 12:19:58
" File:          keymap.vim
" License:       MIT

let mapleader = " "

nnoremap <silent> <leader>or :silent execute("e ".g:vimrc)<cr>
nnoremap <silent> <leader>sr :silent execute("source ".g:vimrc)<cr>

map H ^
map L $

noremap <m-u> ~

inoremap jj <Esc>

nnoremap <leader>z za

nnoremap j gj
nnoremap k gk
nnoremap g<down> j
nnoremap g<up>   k

nnoremap < <<_
nnoremap > >>_

nnoremap Y y$

noremap <c-f> <c-f>M
noremap <c-b> <c-b>M
noremap <c-u> <c-u>zz
noremap <c-d> <c-d>zz
noremap <c-e> 3<c-e>
noremap <c-y> 3<c-y>

nnoremap <expr> zz (winline() == &scrolloff + 1) ? 'zb'
            \ : (winline() == winheight(0) - &scrolloff) ? 'zt' : 'zz'

" nnoremap <expr> ; getcharsearch().forward ? ';' : ','
" nnoremap <expr> , getcharsearch().forward ? ',' : ';'

" nnoremap <silent> <c-down> :move .+1<cr>==
" nnoremap <silent> <c-up> :move .-2<cr>==
" inoremap <silent> <c-down> <esc>:move .+1<cr>==gi
" inoremap <silent> <c-up> <esc>:move .-2<cr>==gi
" vnoremap <silent> <c-down> :move '>+1<cr>gv=gv
" vnoremap <silent> <c-up> :move '<-2<cr>gv=gv
nnoremap <silent> <m-N> :<c-u>move .+1<cr>==
nnoremap <silent> <m-P> :<c-u>move .-2<cr>==
inoremap <silent> <m-N> <esc>:<c-u>move .+1<cr>==gi
inoremap <silent> <m-P> <esc>:<c-u>move .-2<cr>==gi
vnoremap <silent> <m-N> :<c-u>move '>+1<cr>gv=gv
vnoremap <silent> <m-P> :<c-u>move '<-2<cr>gv=gv

nnoremap <silent> tn    :<c-u>tabnew<CR>
nnoremap <silent> tu    :<c-u>enew<CR>
nnoremap <silent> <C-h> :<c-u>call functions#MoveTabOrBuf(0)<CR>
nnoremap <silent> <C-l> :<c-u>call functions#MoveTabOrBuf(1)<CR>
nnoremap <silent> <m-q> :<c-u>bd<CR>
nnoremap <silent> <m-b> <c-^>
nnoremap <leader>wo <c-w>o
nnoremap <leader>wr <c-w>R
nnoremap <leader>wx <c-w>x
nnoremap <leader>w= <c-w>=
nnoremap <leader>wT <c-w>T
nnoremap <leader>w] <c-w>]
nnoremap <leader>wd <c-w>d
nnoremap <leader>wf <c-w>f
nnoremap <leader>wi <c-w>i
nnoremap <leader>wF <c-w>gF
nnoremap <leader>wp <c-w>p
nnoremap <leader>wq <c-w>q
nnoremap <silent> <leader>wh :<c-u>leftabove vsplit<cr>
nnoremap <silent> <leader>wl :<c-u>rightbelow vsplit<cr>
nnoremap <silent> <leader>wj :<c-u>rightbelow split<cr>
nnoremap <silent> <leader>wk :<c-u>leftabove split<cr>
nnoremap <silent> <leader>wH :<c-u>topleft vsplit<cr>
nnoremap <silent> <leader>wL :<c-u>botright vsplit<cr>
nnoremap <silent> <leader>wJ :<c-u>botright split<cr>
nnoremap <silent> <leader>wK :<c-u>topleft split<cr>
nnoremap <m-h> <C-w>h
nnoremap <m-j> <C-w>j
nnoremap <m-k> <C-w>k
nnoremap <m-l> <C-w>l
inoremap <m-h> <esc><C-w>h
inoremap <m-j> <esc><C-w>j
inoremap <m-k> <esc><C-w>k
inoremap <m-l> <esc><C-w>l
tnoremap <m-h> <c-\><c-n><C-w>h
tnoremap <m-j> <c-\><c-n><C-w>j
tnoremap <m-k> <c-\><c-n><C-w>k
tnoremap <m-l> <c-\><c-n><C-w>l
nnoremap <leader>h <c-w>H
nnoremap <leader>l <c-w>L
nnoremap <leader>j <c-w>J
nnoremap <leader>k <c-w>K
nnoremap <silent> <up>       :<c-u>resize +5<CR>
nnoremap <silent> <down>     :<c-u>resize -5<CR>
nnoremap <silent> <left>     :<c-u>vertical resize -5<CR>
nnoremap <silent> <right>    :<c-u>vertical resize +5<CR>

nnoremap <silent> <leader>qn :<c-u>cnext<cr>
nnoremap <silent> <leader>qp :<c-u>cprevious<cr>
nnoremap <silent> <leader>ql :<c-u>clist<cr>

nnoremap <silent> - :<c-u>bprevious<cr>
nnoremap <silent> = :<c-u>bnext<cr>

nnoremap <silent> <leader>tn :<c-u>tnext<cr>
nnoremap <silent> <leader>tp :<c-u>tprevious<cr>
nnoremap <silent> <leader>ts :<c-u>tselect<cr>

inoremap <silent> <c-k> <c-r>=functions#ToggleCaseInInsertMode()<cr>

inoremap <silent> <c-z> <c-o>zz

inoremap <C-a> <home>
inoremap <C-e> <end>
inoremap <C-b> <left>
inoremap <C-f> <right>
inoremap <m-b> <C-left>
inoremap <m-f> <C-right>
inoremap <C-d> <del>
inoremap <c-y> <c-r>"

cnoremap <C-a> <home>
cnoremap <C-e> <end>
cnoremap <C-b> <left>
cnoremap <C-f> <right>
cnoremap <m-b> <C-left>
cnoremap <m-f> <C-right>
cnoremap <C-d> <del>
cnoremap <c-y> <c-r>"

" tnoremap <esc> <C-\><C-n>
tnoremap <C-a> <home>
tnoremap <C-e> <end>
tnoremap <C-b> <left>
tnoremap <C-f> <right>
tnoremap <m-b> <C-left>
tnoremap <m-f> <C-right>
tnoremap <C-d> <del>
tnoremap <c-y> <c-r>"

inoremap <silent> <m-o> <c-o>o
inoremap <silent> <m-O> <c-o>O
cnoremap <c-j> <down>
cnoremap <c-k> <up>

onoremap <silent> inb :<c-u>silent execute "normal! /(\r:nohlsearch\rvi("<cr>
onoremap <silent> ilb :<c-u>silent execute "normal! ?(\r:nohlsearch\rvi("<cr>
onoremap <silent> in[ :<c-u>silent execute "normal! /[\r:nohlsearch\rvi["<cr>
onoremap <silent> il[ :<c-u>silent execute "normal! ?[\r:nohlsearch\rvi["<cr>
onoremap <silent> in] :<c-u>silent execute "normal! /[\r:nohlsearch\rvi["<cr>
onoremap <silent> il] :<c-u>silent execute "normal! ?[\r:nohlsearch\rvi["<cr>
onoremap <silent> in{ :<c-u>silent execute "normal! /{\r:nohlsearch\rvi{"<cr>
onoremap <silent> il{ :<c-u>silent execute "normal! ?{\r:nohlsearch\rvi{"<cr>
onoremap <silent> in} :<c-u>silent execute "normal! /{\r:nohlsearch\rvi{"<cr>
onoremap <silent> il} :<c-u>silent execute "normal! ?{\r:nohlsearch\rvi{"<cr>
onoremap <silent> in" :<c-u>silent execute "normal! /\"\r:nohlsearch\rvi\""<cr>
onoremap <silent> il" :<c-u>silent execute "normal! ?\"\r:nohlsearch\rvi\""<cr>
onoremap <silent> in' :<c-u>silent execute "normal! /'\r:nohlsearch\rvi'"<cr>
onoremap <silent> il' :<c-u>silent execute "normal! ?'\r:nohlsearch\rvi'"<cr>

" find placeholder <++> and insert
nnoremap <silent> <m-i> /<++><CR>:nohlsearch<CR>c4l
inoremap <silent> <m-i> <Esc>/<++><CR>:nohlsearch<CR>c4l
