" Description:   The plugin independent keymaps of vim configuration
" Maintainer:    lwflwf1
" Website:       https://github.com/lwflwf1/vimrc
" Created Time:  2021-04-21 16:54:10
" Last Modified: 2021-04-25 23:54:31
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

" nnoremap <silent> <c-down> :move .+1<cr>==
" nnoremap <silent> <c-up> :move .-2<cr>==
" inoremap <silent> <c-down> <esc>:move .+1<cr>==gi
" inoremap <silent> <c-up> <esc>:move .-2<cr>==gi
" vnoremap <silent> <c-down> :move '>+1<cr>gv=gv
" vnoremap <silent> <c-up> :move '<-2<cr>gv=gv
nnoremap <silent> <m-n> :<c-u>move .+1<cr>==
nnoremap <silent> <m-p> :<c-u>move .-2<cr>==
inoremap <silent> <m-n> <esc>:<c-u>move .+1<cr>==gi
inoremap <silent> <m-p> <esc>:<c-u>move .-2<cr>==gi
vnoremap <silent> <m-n> :<c-u>move '>+1<cr>gv=gv
vnoremap <silent> <m-p> :<c-u>move '<-2<cr>gv=gv

nnoremap <silent> tn :<c-u>tabnew<CR>
nnoremap <silent> tu :<c-u>enew<CR>
nnoremap <silent> <C-h> :<c-u>call MoveTabOrBuf(0)<CR>
nnoremap <silent> <C-l> :<c-u>call MoveTabOrBuf(1)<CR>
nnoremap <silent> <m-q> :<c-u>bd<CR>
nnoremap <leader>wo <c-w>o
nnoremap <leader>wr <c-w>R
nnoremap <leader>wx <c-w>x
nnoremap <silent> <leader>wh :<c-u>leftabove vsplit<cr>
nnoremap <silent> <leader>wl :<c-u>rightbelow vsplit<cr>
nnoremap <silent> <leader>wj :<c-u>rightbelow split<cr>
nnoremap <silent> <leader>wk :<c-u>leftabove split<cr>
nnoremap <m-h> <C-w>h
nnoremap <m-j> <C-w>j
nnoremap <m-k> <C-w>k
nnoremap <m-l> <C-w>l
nnoremap <leader>h <c-w>H
nnoremap <leader>l <c-w>L
nnoremap <leader>j <c-w>J
nnoremap <leader>k <c-w>K
nnoremap <silent> <up> :<c-u>resize +5<CR>
nnoremap <silent> <down> :<c-u>resize -5<CR>
nnoremap <silent> <left> :<c-u>vertical resize -5<CR>
nnoremap <silent> <right> :<c-u>vertical resize +5<CR>
nnoremap <silent> <leader>qn :<c-u>cnext<cr>
nnoremap <silent> <leader>qp :<c-u>cprevious<cr>

nnoremap <silent> - :<c-u>bprevious<cr>
nnoremap <silent> = :<c-u>bnext<cr>

" nnoremap <expr> zz (winline() == (winheight(0)+1) / 2) ?
"     \ 'zt' : (winline() == &scrolloff + 1) ? 'zb' : 'zz'
" noremap <expr> <C-f> max([winheight(0) - 2, 1])
"     \ ."\<C-d>".(line('w$') >= line('$') ? "L" : "H")
" noremap <expr> <C-b> max([winheight(0) - 2, 1])
"     \ ."\<C-u>".(line('w0') <= 1 ? "H" : "L")
" noremap <expr> <C-e> (line("w$") >= line('$') ? "j" : "3\<C-e>")
" noremap <expr> <C-y> (line("w0") <= 1         ? "k" : "3\<C-y>")

inoremap <silent> <c-k> <c-r>=ToggleCaseInInsertMode()<cr>

inoremap <silent> <c-z> <c-o>zz

inoremap <C-a> <home>
inoremap <C-e> <end>
inoremap <C-d> <del>
inoremap <silent> <m-o> <c-o>o
inoremap <silent> <m-O> <c-o>O
cnoremap <C-a> <home>
cnoremap <C-e> <end>
cnoremap <C-d> <del>

inoremap <C-h> <left>
inoremap <C-l> <right>
inoremap <m-h> <C-left>
inoremap <m-l> <C-right>
cnoremap <C-h> <left>
cnoremap <C-l> <right>
cnoremap <m-h> <C-left>
cnoremap <m-l> <C-right>
cnoremap <c-j> <down>
cnoremap <c-k> <up>

tnoremap <Esc> <C-\><C-n>
tnoremap <C-a> <home>
tnoremap <C-e> <end>
tnoremap <C-d> <del>
tnoremap <C-h> <left>
tnoremap <C-l> <right>
tnoremap <m-h> <C-left>
tnoremap <m-l> <C-right>

onoremap <silent> in( :<c-u>silent execute("normal! /(\r:nohlsearch\rvi(")<cr>
onoremap <silent> il( :<c-u>silent execute("normal! ?(\r:nohlsearch\rvi(")<cr>
onoremap <silent> in[ :<c-u>silent execute("normal! /[\r:nohlsearch\rvi[")<cr>
onoremap <silent> il[ :<c-u>silent execute("normal! ?[\r:nohlsearch\rvi[")<cr>
onoremap <silent> in{ :<c-u>silent execute("normal! /{\r:nohlsearch\rvi{")<cr>
onoremap <silent> il{ :<c-u>silent execute("normal! ?{\r:nohlsearch\rvi{")<cr>
onoremap <silent> in" :<c-u>silent execute("normal! /\"\r:nohlsearch\rvi\"")<cr>
onoremap <silent> il" :<c-u>silent execute("normal! ?\"\r:nohlsearch\rvi\"")<cr>
onoremap <silent> in' :<c-u>silent execute("normal! /'\r:nohlsearch\rvi'")<cr>
onoremap <silent> il' :<c-u>silent execute("normal! ?'\r:nohlsearch\rvi'")<cr>

" find placeholder <++> and insert
nnoremap <silent> <m-i> /<++><CR>:nohlsearch<CR>c4l
inoremap <silent> <m-i> <Esc>/<++><CR>:nohlsearch<CR>c4l

augroup q_on_help_group
    autocmd!
    autocmd FileType help nnoremap <silent> <buffer> q :bwipeout!<cr>
augroup END

" nnoremap <silent> <leader>n :silent execute "normal! :grep! -F <cword>\r:copen\r"<cr>
if !exists("g:plugs")
    " nnoremap <silent> <leader>g :silent execute "normal! :vimgrep /".expand("<cword>")."/j ./*\r:copen\r"<cr>
endif
