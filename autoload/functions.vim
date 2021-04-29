" Description   : functions of vimrc
" Maintainer    : lwflwf1
" Website       : https://github.com/lwflwf1/vimrc.com
" Created Time  : 2021-04-26 19:55:52
" Last Modified : 2021-04-30 16:03:33
" File          : functions.vim
" License       : MIT

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
function! functions#UpdateLastModified() abort
  let l:cursor_positon = getcurpos()
  %s/\v(Last Modified\s*:\s+)%(%(\d|-|:|\s)+)/\=submatch(1).strftime("%Y-%m-%d %H:%M:%S")/e
  call setpos('.', l:cursor_positon)
endfunction

function! functions#MoveTabOrBuf(direction) abort

  let s:exclude_ft = ["coc-explorer", "vista", "far", "leaderf"]
  if index(s:exclude_ft, &ft) != -1 && winnr('$') != 1
    return
  endif

  if &ft ==# "floaterm"
    if a:direction == 0
      exec "FloatermNext"
    else
      exec "FloatermPrev"
    endif
    return
  endif

  if tabpagenr('$') > 1
    if a:direction == 0
      exec 'tabprevious'
    elseif a:direction == 1
      exec 'tabnext'
    endif
  else
    if a:direction == 0
      exec 'bprevious'
    elseif a:direction == 1
      exec 'bnext'
    endif
  endif
endfunction

function! functions#SetTitle() abort
  call setline(1, "\#!/usr/bin/python")
  call setline(2, "\# -*- encoding=utf8 -*-")
  call setline(3, "\"\"\"")
  call setline(4, "\# @Author       : Gong Yingfan")
  call setline(5, "\# @Created Time : ".strftime("%Y-%m-%d %H:%M:%S"))
  call setline(6, "\# @Description  : ")
  call setline(7, "\"\"\"")
  normal! Gk$
  startinsert!
endfunction

function! functions#GetMode() abort
    let l:m = mode()
    if &ft ==# 'help'
        return 'HELP'
    elseif &ft ==# 'sessionlist'
        return 'SessionList'
    elseif has_key(s:mode_dict, m)
        return s:mode_dict[m]
    else
        return ''
    endif
endfunction

function! functions#ToggleCaseInInsertMode() abort
  let l:col = col(".")
  let l:is_firstchar = !l:col || getline('.')[l:col - 2] =~# '\s'
  if !l:is_firstchar
    call cursor(0, l:col - 1)
  endif
  execute "normal! viw~"
  call cursor(0, l:col)
  return ''
endfunction
