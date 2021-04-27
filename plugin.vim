" Description:   The Plugin settings of vim configuration
" Maintainer:    lwflwf1
" Website:       https://github.com/lwflwf1/vimrc
" Created Time:  2021-04-21 16:55:35
" Last Modified: 2021-04-28 02:43:54
" File:          plugin.vim
" License:       MIT

let s:dein_path = g:dein_dir.'/repos/github.com/Shougo/dein.vim'
let &runtimepath .= ','.s:dein_path
let g:dein#install_max_processes = 12
let g:dein#auto_recache = 1
command! -nargs=* DeinUpdate     call dein#update(<f-args>)
command! -nargs=* DeinInstall    call dein#install(<f-args>)
command! -nargs=* DeinRecache    call dein#recache_runtimepath(<f-args>)
command! -nargs=0 DeinClean      call map(dein#check_clean(), "delete(v:val, 'rf')")
command! -nargs=0 DeinClearState call dein#clear_state()
command! -nargs=0 DeinCheckClean execute 'echo dein#check_clean()'

if dein#load_state(g:dein_dir)
call dein#begin(g:dein_dir)

call dein#add(s:dein_path)

call dein#add('ajmwagar/vim-deus')
call dein#add( 'joshdick/onedark.vim')
" call dein#add('romgrk/doom-one.vim')
call dein#add( 'ryanoasis/vim-devicons')
" call dein#add( 'vim-airline/vim-airline')
" call dein#add( 'vim-airline/vim-airline-themes')
call dein#add('itchyny/lightline.vim')
call dein#add('mengelbrecht/lightline-bufferline')
" call dein#add('romgrk/barbar.nvim')
" call dein#add('theniceboy/eleline.vim')
" call dein#add('glepnir/spaceline.vim')
" call dein#add('liuchengxu/eleline.vim')
" call dein#add('bagrat/vim-buffet')
call dein#add( 'tpope/vim-repeat')
call dein#add( 'mzlogin/vim-markdown-toc')
" coc.nvim requires node 10.12+
call dein#add( 'neoclide/coc.nvim', {
  \ 'if': "has('nvim-0.3.2') || has('patch-8.0.1453')",
  \ 'rev': 'release',
  \ })
" vista.vim requires neovim or vim 8.0.27+ if you want ctags to run asynchonously
" vista.vim requires fzf 0.22+ if you want to use fzf
" vista.vim only support universal-ctags
call dein#add( 'liuchengxu/vista.vim', {
  \ 'lazy': 1,
  \ 'on_cmd': ['Vista', 'Vista!', 'Vista!!'],
  \ 'on_event': 'BufReadPre'
  \ })
call dein#add( 'skywind3000/vim-dict', {
  \ 'lazy': 1,
  \ 'on_event': 'InsertEnter'
  \ })
call dein#add( 'easymotion/vim-easymotion', {
  \ 'lazy': 1,
  \ 'on_map': '<Plug>(easymotion'
  \ })
call dein#add( 'justinmk/vim-sneak', {
  \ 'lazy': 1,
  \ 'on_map': '<Plug>Sneak'
  \ })
call dein#add( 'sheerun/vim-polyglot', {
  \ 'lazy': 1,
  \ 'on_event': 'BufReadPre'
  \ })
call dein#add( 'tpope/vim-surround', {
  \ 'lazy': 1,
  \ 'on_map': {'n': ['cs', 'ds', 'ys', 'cS', 'yS'], 'v': ['S', 'gS']}
  \ })
call dein#add( 'tpope/vim-fugitive', {
  \ 'lazy': 1,
  \ 'on_event': 'BufReadPre'
  \ })
" \ 'on_cmd': ['G', 'Git', 'Git', 'Gwrite', 'Gread', 'Gdiffsplit']
call dein#add( 'tpope/vim-commentary', {
  \ 'lazy': 1,
  \ 'on_event': 'BufReadPost'
  \ })
" \ 'on_map': 'gc'
call dein#add( 'airblade/vim-gitgutter', {
  \ 'lazy': 1,
  \ 'on_event': 'BufReadPre'
  \ })
call dein#add( 'AndrewRadev/switch.vim', {
  \ 'lazy': 1,
  \ 'on_cmd': 'Switch'
  \ })
call dein#add( 'Yggdroot/indentLine', {
  \ 'lazy': 1,
  \ 'on_event': 'BufReadPre'
  \ })
call dein#add( 'vhda/verilog_systemverilog.vim', {
  \ 'lazy': 1,
  \ 'on_event': 'BufReadPre'
  \ })
call dein#add( 'ludovicchabant/vim-gutentags', {
  \ 'lazy':1,
  \ 'on_event': 'BufReadPost'
  \ })
call dein#add( 'yianwillis/vimcdoc', {
  \ 'lazy': 1,
  \ 'on_event': 'BufReadPre'
  \ })
call dein#add( 'gcmt/wildfire.vim', {
  \ 'lazy': 1,
  \ 'on_map': {'n': '<Plug>(wildfire-fuel)', 'v': '<Plug>(wildfire-water)'}
  \ })
call dein#add( 'mg979/vim-visual-multi', {
  \ 'lazy': 1,
  \ 'on_map': ['<c-j>', '<c-k>', '<c-n>'],
  \ 'on_source': 'vim-surround',
  \ 'rev': 'master'
  \ })
call dein#add( 'honza/vim-snippets', {
  \ 'lazy': 1,
  \ 'on_event': 'InsertEnter'
  \ })
call dein#add( 'RRethy/vim-illuminate', {
  \ 'lazy': 1,
  \ 'on_event': 'BufReadPre'
  \ })
call dein#add( 'dhruvasagar/vim-table-mode', {
  \ 'lazy': 1,
  \ 'on_cmd': 'TableModeEnable',
  \ 'on_ft': 'markdown'
  \ })
call dein#add( 'dkarter/bullets.vim', {
  \ 'lazy': 1,
  \ 'on_ft': ['markdown', 'text']
  \ })
call dein#add( 'svermeulen/vim-subversive', {
  \ 'lazy': 1,
  \ 'on_map': '<plug>(SubversiveSubstitute'
  \ })
call dein#add( 'brooth/far.vim', {
  \ 'lazy': 1,
  \ 'on_cmd': 'Far'
  \ })
call dein#add( 'junegunn/vim-easy-align', {
  \ 'lazy': 1,
  \ 'on_map': '<plug>(EasyAlign)'
  \ })
call dein#add( 'liuchengxu/vim-which-key', {
  \ 'lazy': 1,
  \ 'on_map': ['WhichKey', 'WhichKey!']
  \ })
call dein#add( 'mbbill/undotree', {
  \ 'lazy': 1,
  \ 'on_cmd': 'UndotreeToggle'
  \ })
call dein#add( 'skywind3000/asyncrun.vim', {
  \ 'if': "has('nvim') || v:version >=# 800",
  \ 'lazy': 1,
  \ 'on_cmd': 'AsyncRun',
  \ })
call dein#add( 'skywind3000/asynctasks.vim', {
  \ 'if': "has('nvim') || v:version >=# 800",
  \ 'lazy': 1,
  \ 'on_cmd': ['AsyncTask', 'AsyncTaskList', 'AsyncTaskEdit'],
  \ 'on_source': 'asyncrun.vim'
  \ })
call dein#add( 'skywind3000/asyncrun.extra', {
  \ 'if': "has('nvim') || v:version >=# 800",
  \ 'lazy': 1,
  \ 'on_cmd': 'AsyncRun',
  \ 'on_source': 'asyncrun.vim'
  \ })

call dein#add( 'iamcco/markdown-preview.nvim', {
  \ 'if': "has('nvim') || v:version >=# 801",
  \ 'lazy': 1,
  \ 'on_ft': 'markdown',
  \ 'hook_post_update': 'call mkdp#util#install()'
  \ })

call dein#add( 'voldikss/vim-floaterm', {
  \ 'if': "has('nvim-0.4') || v:version >=# 802",
  \ 'lazy': 1,
  \ 'on_cmd': ['FloatermNew', 'FloatermToggle', 'FloatermSend']
  \ })
call dein#add( 'voldikss/LeaderF-floaterm', {
  \ 'if': "has('nvim-0.4') || v:version >=# 802",
  \ 'lazy': 1,
  \ 'on_cmd': 'Leaderf floaterm',
  \ 'on_source':['vim-floaterm', 'LeaderF'],
  \ })

call dein#add( 'Yggdroot/LeaderF', {
  \ 'if': "has('python3')",
  \ 'lazy': 1,
  \ 'on_map': '<leaderf>f',
  \ 'hook_post_update': 'LeaderfInstallCExtension'
  \ })
call dein#add( 'Yggdroot/LeaderF-marks', {
  \ 'if': "has('python3')",
  \ 'lazy': 1,
  \ 'on_cmd': 'LeaderfMarks',
  \ 'on_source': 'LeaderF'
  \ })

call dein#add( 'numirias/semshi', {
  \ 'if': "has('python3') && has('nvim')",
  \ 'lazy': 1,
  \ 'on_ft': 'python',
  \ 'hook_post_update': 'UpdateRemotePlugins'
  \ })

call dein#local("C:/disk_2/vim-session-manager", {'frozen': 1, 'merged': 0})
call dein#local("C:/disk_2/vim-smart-hlsearch", {'frozen': 1, 'merged': 0})

" call dein#add( 'haya14busa/incsearch.vim')
" call dein#add( 'kana/vim-textobj-user')
" call dein#add( 'preservim/nerdtree')
" call dein#add( 'Xuyuanp/nerdtree-git-plugin')
" call dein#add( 'tiagofumo/vim-nerdtree-syntax-highlight')
" call dein#add( 'skywind3000/vim-terminal-help')
" call dein#add( 'skywind3000/vim-auto-popmenu')
" call dein#add( 'Linfee/ultisnips-zh-doc')
" call dein#add( 'SirVer/ultisnips')
" call dein#add( 'codota/tabnine-vim')

call dein#end()
call dein#save_state()
endif
if dein#check_install()
  call dein#install()
endif
unlet s:dein_path
source c:/disk_2/vim-session-manager/plugin/vim-session-manager.vim
source c:/disk_2/vim-smart-hlsearch/plugin/vim-smart-hlsearch.vim
" if !exists("g:plugs")
"     " mode, buffer number, file path, preview window flag,
"     " modified flag, read only flag
"     set statusline=\ %{functions#GetMode()}\ \|\ [%n]\ %F\ %w\ %m\ %r
"     if exists('g:loaded_vim_session_manager')
"         set statusline+=\ %{SessionStatusLine()}
"     endif
"     set statusline+=%=
"     " filetype, percentage, line number, total line numbers, column number
"     set statusline+=%y\ %p%%\ ☰\ %l/%L\ :%c
" endif

if dein#tap('lightline.vim')
  let s:special_filetypes = ['coc-explorer', 'vista', 'sessionlist', 'help', 'fugitive']
  function Gitinfo() abort
    if index(s:special_filetypes, &ft) !=# -1
      return ''
    endif
    let l:gitname = ''
    let l:gitsummary = []
    if exists('g:loaded_gitgutter') | let l:gitsummary = GitGutterGetHunkSummary() | endif
    if exists('g:loaded_fugitive') | let l:gitname = FugitiveHead() | endif
    if empty(l:gitname)
      return ''
    elseif empty(l:gitsummary)
      return "\ue0a0 ".l:gitname
    elseif winwidth(0) > 70
      return "\ue0a0 ".l:gitname.': '.printf('+%d ~%d -%d', l:gitsummary[0], l:gitsummary[1], l:gitsummary[2])
    else
      return printf('+%d ~%d -%d', l:gitsummary[0], l:gitsummary[1], l:gitsummary[2])
    endif
  endfunction

  function MyLightlineFileType() abort
    return index(s:special_filetypes, &ft) !=# -1 || &ft ==# ''? '' : WebDevIconsGetFileTypeSymbol().' '.&ft
  endfunction

  function MyLightlineReadonly() abort
    if index(s:special_filetypes, &ft) !=# -1
      return ''
    endif
    if &readonly
      return 'RO'
    else
      return ''
    endif
  endfunction

  function MyLightlineMode() abort
    return index(s:special_filetypes, &ft) !=# -1 ?  &ft : lightline#mode()
  endfunction

  function MyLightlineFilename() abort
    if index(s:special_filetypes, &ft) !=# -1
      return ''
    endif
    let l:filename = expand('%:t')
    let l:modified = &modified ? ' +' : ''
    return l:filename.l:modified
  endfunction

  function MyLightlineSession() abort
    if exists('g:loaded_vim_session_manager') && winwidth(0) > 90
      return SessionStatusLine()
    endif
    return ''
  endfunction

  function MyLightlineFileformat() abort
    if index(s:special_filetypes, &ft) !=# -1 || winwidth(0) < 110
      return ''
    endif
    return &fileformat
  endfunction

  function MyLightlineFileencoding() abort
    if index(s:special_filetypes, &ft) !=# -1 || winwidth(0) < 100
      return ''
    endif
    return &fileencoding
  endfunction

  function MyLightlineInactiveMode() abort
    if index(s:special_filetypes, &ft) !=# -1
      return &ft
    endif
    return expand('%:t')
  endfunction

  function! MyLightlineCocStatus()
    let info = get(b:, 'coc_diagnostic_info', {})
    let msgs = []
    if get(info, 'error', 0)
      call add(msgs, "\uf467 " . info['error'])
    endif
    if get(info, 'warning', 0)
      call add(msgs, "\uf071 " . info['warning'])
    endif
    return trim(join(msgs, ' ') . ' ' . get(g:, 'coc_status', ''))
  endfunction

  " function! s:trim(str)
  "   if exists('*trim')
  "     return trim(a:str)
  "   endif
  "   return substitute(a:str, '\s\+$', '', '')
  " endfunction

  let g:lightline = {
    \ 'colorscheme': 'one',
    \ 'mode_map': {
    \   'c': 'NORMAL',
    \ },
    \ 'component': {
    \   'lineinfo': '%l/%L:%c%<',
    \ },
    \ 'component_function': {
    \   'session'      : 'MyLightlineSession',
    \   'git'          : 'Gitinfo',
    \   'filename'     : 'MyLightlineFilename',
    \   'mode'         : 'MyLightlineMode',
    \   'filetype'     : 'MyLightlineFileType',
    \   'readonly'     : 'MyLightlineReadonly',
    \   'fileencoding' : 'MyLightlineFileencoding',
    \   'fileformat'   : 'MyLightlineFileformat',
    \   'inactivemode' : 'MyLightlineInactiveMode',
    \   'cocstatus'    : 'MyLightlineCocStatus',
    \ },
    \ 'component_expand': {
    \    'buffers': 'lightline#bufferline#buffers',
    \ },
    \ 'component_type': {
    \   'buffers': 'tabsel',
    \ },
    \ 'tabline': {
    \   'left': [['buffers']],
    \   'right': [['close']],
    \ }
    \ }

  let g:lightline.active = {
    \ 'left': [['mode', 'paste'],
    \          ['readonly', 'git', 'filename', 'session', 'cocstatus',]],
    \ 'right': [['percent'],
    \           ['lineinfo'],
    \           ['spell', 'filetype', 'fileencoding', 'fileformat']]
    \ }

  let g:lightline.inactive = {
    \ 'left': [['inactivemode']],
    \ 'right': [['percent'],
    \           ['lineinfo']],
    \ }
endif

if dein#tap('lightline-bufferline')
    let g:lightline#bufferline#enable_devicons = 1
    let g:lightline#bufferline#unicode_symbols = 1
    let g:lightline#bufferline#show_number = 1
    " let g:lightline.component_raw = {'buffers': 1}
endif

if dein#tap('spaceline.vim')
  let g:spaceline_diff_tool = 'git-gutter'
  let g:spaceline_seperate_style = 'arrow-fade'
  let g:spaceline_colorscheme = 'one'
  " let g:spaceline_diagnostic_warnsign = 'X'
endif

if dein#tap('vim-buffet')
  let g:buffet_show_index = 1
  let g:buffet_use_devicons = 1
  let g:buffet_powerline_separators = 1
  let g:buffet_tab_icon = "\uf00a"
  let g:buffet_left_trunc_icon = "\uf0a8"
  let g:buffet_right_trunc_icon = "\uf0a9"
endif

if dein#tap('vim-easymotion')
  " let g:Easymotion_use_upper = 1
  let g:Easymotion_do_mapping       = 0
  let g:Easymotion_smartcase        = 1
  let g:Easymotion_smartsign_us     = 1
  let g:EasyMotion_space_jump_first = 1
  map gj <Plug>(easymotion-j)
  map gk <Plug>(easymotion-k)
  map gs <Plug>(easymotion-s)
  map gw <Plug>(easymotion-w)
  map ge <Plug>(easymotion-e)
  map gb <Plug>(easymotion-b)
  map gW <Plug>(easymotion-W)
  map gE <Plug>(easymotion-E)
  map gB <Plug>(easymotion-B)
  map gJ <Plug>(easymotion-eol-j)
  map gK <Plug>(easymotion-eol-k)
  map gl <Plug>(easymotion-jumptoanywhere)
  " nmap ; <Plug>(easymotion-next)
  " nmap , <Plug>(easymotion-prev)
  if dein#tap('coc.nvim')
    augroup easymotion_coc_group
      autocmd!
      autocmd User EasyMotionPromptBegin silent! CocDisable
      autocmd User EasyMotionPromptEnd   silent! CocEnable
    augroup END
  endif
endif

if dein#tap('incsearch.vim')
  " map /  <Plug>(incsearch-forward)
  " map ?  <Plug>(incsearch-backward)
  " map g/ <Plug>(incsearch-stay)

  " let g:incsearch#auto_nohlsearch = 1
  " nmap n  <Plug>(incsearch-nohl-n)
  " nmap N  <Plug>(incsearch-nohl-N)
  " nmap *  <Plug>(incsearch-nohl-*)
  " nmap #  <Plug>(incsearch-nohl-#)
  " nmap g* <Plug>(incsearch-nohl-g*)
  " nmap g# <Plug>(incsearch-nohl-g#)
endif

if dein#tap('vim-subversive')
  nmap s  <plug>(SubversiveSubstitute)
  xmap s  <plug>(SubversiveSubstitute)
  nmap ss <plug>(SubversiveSubstituteLine)
  nmap S  <plug>(SubversiveSubstituteToEndOfLine)

  nmap <leader>s  <plug>(SubversiveSubstituteRange)
  xmap <leader>s  <plug>(SubversiveSubstituteRange)
  nmap <leader>ss <plug>(SubversiveSubstituteWordRange)
endif

if dein#tap('vim-deus')
  colorscheme deus
endif

if dein#tap('undotree')
  nnoremap <silent> <leader>u :UndotreeToggle<cr>
endif

if dein#tap('vim-which-key')
  if has('nvim-0.4.2') || has('patch-8.1.1615')
    let g:which_key_use_floating_win = 1
  endif
  let g:which_key_timeout = 300
  let g:which_key_fallback_to_native_key=1
  " xmap s <plug>(SubversiveSubstituteRange)
  nnoremap <silent> <leader> :<c-u>WhichKey '<space>'<cr>
  nnoremap <silent> g :<c-u>WhichKey 'g'<cr>
  vnoremap <silent> <leader> :<c-u>WhichKeyVisual '<space>'<cr>
  vnoremap <silent> g :<c-u>WhichKeyVisual 'g'<cr>
endif

if dein#tap('vim-easy-align')
  nmap ga <Plug>(EasyAlign)
  xmap ga <Plug>(EasyAlign)
endif

if dein#tap('vim-auto-popmenu')
  let g:apc_enable_ft = {'markdown':1, 'text':1}
  let g:apc_enable_ft = {'*':1}
endif

if dein#tap('ultisnips')
  let g:UltiSnipsExpandTrigger="<m-e>"
  let g:UltiSnipsJumpForwardTrigger="<m-e>"
  let g:UltiSnipsSnippetDir=stdpath('config').'\Ultisnips'
  let g:UltiSnipsSnippetDirectories=[stdpath('config').'\Ultisnips']
  let g:UltiSnipsEditSplit="vertical"
endif

if dein#tap('coc.nvim')
  if has('nvim-0.4.0') || has('patch-8.2.0750')
    nnoremap <silent><nowait><expr> <C-f> coc#float#has_scroll() ? coc#float#scroll(1) : "\<C-f>"
    nnoremap <silent><nowait><expr> <C-b> coc#float#has_scroll() ? coc#float#scroll(0) : "\<C-b>"
    inoremap <silent><nowait><expr> <C-f> coc#float#has_scroll() ? "\<c-r>=coc#float#scroll(1)\<cr>" : "\<Right>"
    inoremap <silent><nowait><expr> <C-b> coc#float#has_scroll() ? "\<c-r>=coc#float#scroll(0)\<cr>" : "\<Left>"
    vnoremap <silent><nowait><expr> <C-f> coc#float#has_scroll() ? coc#float#scroll(1) : "\<C-f>"
    vnoremap <silent><nowait><expr> <C-b> coc#float#has_scroll() ? coc#float#scroll(0) : "\<C-b>"
  endif

" Use tab for trigger completion with characters ahead and navigate.
" NOTE: Use command ':verbose imap <tab>' to make sure tab is not mapped by
" other plugin before putting this into your config.
inoremap <silent><expr> <TAB>
  \ pumvisible() ? "\<C-n>" :
  \ <SID>check_back_space() ? "\<TAB>" :
  \ coc#refresh()
inoremap <expr><S-TAB> pumvisible() ? "\<C-p>" : "\<C-h>"

function! s:check_back_space() abort
  let col = col('.') - 1
  return !col || getline('.')[col - 1]  =~# '\s'
endfunction

" " Make <CR> auto-select the first completion item and notify coc.nvim to
" " format on enter, <CR> could be remapped by other vim plugin
inoremap <silent><expr> <CR> pumvisible() ? coc#_select_confirm()
                              \: "\<C-g>u\<CR>\<c-r>=coc#on_enter()\<CR>"
" Use <leader>x for convert visual selected code to snippet
xmap <leader>x  <Plug>(coc-convert-snippet)

" Use <C-j> for both expand and jump (make expand higher priority.)
" imap <C-j> <Plug>(coc-snippets-expand-jump)

" let g:coc_snippet_next = '<tab>'

inoremap <silent><expr> <c-p> coc#refresh()

"diagnostics
nmap <silent> <leader>dk <Plug>(coc-diagnostic-prev)
nmap <silent> <leader>dj <Plug>(coc-diagnostic-next)
nmap <silent> <leader>dd <Plug>(coc-diagnostic-info)

nnoremap <silent> <leader>p  :<C-u>CocList -A --normal yank<cr>

nnoremap <silent> tt :CocCommand explorer<CR>

nmap <silent> gd <Plug>(coc-definition)
nmap <silent> gr <Plug>(coc-references)
nmap <silent> gi <Plug>(coc-Implementation)
nmap <silent> gy <Plug>(coc-type-difinition)

" Use K to show documentation in preview window.
nnoremap <silent> K :call <SID>show_documentation()<CR>
function! s:show_documentation()
  if (index(['vim','help'], &filetype) >= 0)
    execute 'h '.expand('<cword>')
  elseif (coc#rpc#ready())
    call CocActionAsync('doHover')
  else
    execute '!' . &keywordprg . " " . expand('<cword>')
  endif
endfunction

nnoremap <silent> <leader>tt :CocCommand translator.popup<CR>

" Highlight the symbol and its references when holding the cursor.
" autocmd CursorHold * silent call CocActionAsync('highlight')

" Symbol renaming.
nmap <leader>rn <Plug>(coc-rename)
nnoremap <leader>cs :CocSearch -S -w 

" Applying codeAction to the selected region.
" Example: `<leader>aap` for current paragraph
xmap <leader>c  <Plug>(coc-codeaction-selected)
nmap <leader>c  <Plug>(coc-codeaction-selected)
nmap <leader>cc <Plug>(coc-codeaction)

" Map function and class text objects
" NOTE: Requires 'textDocument.documentSymbol' support from the language server.
xmap if <Plug>(coc-funcobj-i)
omap if <Plug>(coc-funcobj-i)
xmap af <Plug>(coc-funcobj-a)
omap af <Plug>(coc-funcobj-a)
xmap ic <Plug>(coc-classobj-i)
omap ic <Plug>(coc-classobj-i)
xmap ac <Plug>(coc-classobj-a)
omap ac <Plug>(coc-classobj-a)

"coc-explorer needs >= vim 8.1.1418 or >= neovim 0.3.1
let g:coc_global_extensions = [
  \ 'coc-json',
  \ 'coc-vimlsp',
  \ 'coc-pyright',
  \ 'coc-explorer',
  \ 'coc-pairs',
  \ 'coc-highlight',
  \ 'coc-sh',
  \ 'coc-lists',
  \ 'coc-yank',
  \ 'coc-translator',
  \ 'coc-snippets',
  \ 'coc-jedi',
  \ 'coc-tabnine',
  \ 'coc-tasks',
  \ ]

endif

if dein#tap('vim-gitgutter')

let g:gigutter_enable = 1
let g:gitgutter_highlight_lines = 0
let g:gitgutter_highlight_linenrs = 1
let g:gitgutter_map_keys = 0
let g:gitgutter_max_signs = 500
let g:gitgutter_preview_win_floating = 1
let g:gitgutter_git_executable = 'C:\disk_1\Git\bin\git.exe'

command! GitInQuickFix GitGutterQuickFix | copen

nnoremap <silent> <leader>gk :GitGutterPrevHunk<cr>
nnoremap <silent> <leader>gj :GitGutterNextHunk<cr>
nnoremap <silent> <leader>gh :GitGutterPreviewHunk<cr>
nnoremap <silent> <leader>gu :GitGutterUndoHunk<cr>
nnoremap <silent> <leader>gs :GitGutterStageHunk<cr>
nnoremap <silent> <leader>gq :GitInQuickFix<cr>
nnoremap <silent> <leader>gf :GitGutterFold<cr>
" omap ih <Plug>(GitGutterTextObjectInnerPending)

" omap ah <Plug>(GitGutterTextObjectOuterPending)
" xmap ih <Plug>(GitGutterTextObjectInnerVisual)
" xmap ah <Plug>(GitGutterTextObjectOuterVisual)

endif

if dein#tap('vim-fugitive')

nnoremap <silent> <leader>gw :Gwrite<cr>
nnoremap <silent> <leader>gc :Git commit<cr>
nnoremap <silent> <leader>gr :Gread<cr>
nnoremap <silent> <leader>gd :Gdiffsplit<cr>
nnoremap <silent> <leader>gb :Git blame<cr>
nnoremap <silent> <leader>gg :Git<cr>
nnoremap <silent> <leader>gl :Git log<cr>
nnoremap <silent> <leader>ge :Git rebase

endif

if dein#tap('vim-sneak')

map f <Plug>Sneak_s
map F <Plug>Sneak_S

endif

if dein#tap('LeaderF')
let g:Lf_Ctags = 'C:/disk_1/ctags/ctags.exe'
let g:Lf_IgnoreCurrentBufferName = 1
let g:Lf_ShowDevIcons = 1
let g:Lf_WildIgnore ={
  \ 'dir'  : ['.svn', '.git', '.hg', ],
  \ 'file' : ['*.exe', '*.o', '*.so', '*.py[co]'],
  \ }
let g:Lf_StlColorscheme = 'powerline'
let g:Lf_PreviewResult = {
  \ 'File': 0,
  \ 'Buffer': 0,
  \ 'Mru': 0,
  \ 'Tag': 0,
  \ 'BufTag': 1,
  \ 'Function': 1,
  \ 'Line': 0,
  \ 'Colorscheme': 1,
  \ 'Rg': 0,
  \ 'Gtags': 0
  \}
let g:Lf_RootMarkers = ['.git', '.svn', '.hg', '.root', '.project']
let g:Lf_WorkingDirectoryMode = 'AF'
" if has('nvim-0.4.2') || has('patch-8.1.1615')
" let g:Lf_WindowPosition = 'popup'
" let g:LF_PreviewInPopup = 1
" endif

" let s:leaderf_function_on = 0
" function s:leaderfFunctionToggle() abort
"   keepalt noautocmd windo if &ft ==# 'leaderf' | bwipeout! | endif
"   if s:leaderf_function_on
"     let s:leaderf_function_on = 0
"   elseif !s:leaderf_function_on
"     LeaderfFunction!
"     let s:leaderf_function_on = 1
"   endif
" endfunction

let g:Lf_ShortcutF = "<leader>ff"
nnoremap <leader>fF :LeaderfFile 
nnoremap <silent> <leader>fm :LeaderfMru<CR>
nnoremap <silent> <leader>fu :LeaderfFunction<CR>
" nnoremap <silent> <F12> :call <SID>leaderfFunctionToggle()<CR>
nnoremap <silent> <leader>fl :LeaderfLine<CR>
nnoremap <silent> <leader>fL :LeaderfLineAll<CR>
nnoremap <silent> <leader>fw :Leaderf line --cword<CR>
nnoremap <silent> <leader>fr :Leaderf --recall<CR>
nnoremap <silent> <leader>ft :LeaderfBufTagAll<CR>
nnoremap <silent> <leader>fb :LeaderfBufTag<cr>
" nnoremap <silent> <leader>fs :Leaderf floaterm<cr>
nnoremap <silent> <leader>fc :LeaderfCommand<cr>
nnoremap <silent> <leader>fh :LeaderfHistoryCmd<cr>
nnoremap <silent> <leader>fq :LeaderfQuickFix<cr>
nnoremap <silent> <leader>fk :LeaderMarks<cr>
" nnoremap <silent> <leader>rg :Leaderf rg<CR>
nnoremap <silent> <leader>rg :LeaderfRgInteractive<CR>
nmap <silent> <leader>rw <Plug>LeaderfRgCwordLiteralBoundary<cr>
xmap <silent> gf <Plug>LeaderfRgVisualLiteralNoBoundary<cr>
" xnoremap <silent> gf :<c-u><c-r>=printf("Leaderf! rg -F -e %s ", leaderf#Rg#visual())<cr><cr>
endif

if dein#tap('vim-airline')
  "adding to vim-airline's tabline
  let g:webdevicons_enable_airline_tabline = 1
  "adding to vim-airline's statusline
  let g:webdevicons_enable_airline_statusline = 1

  let g:airline#extensions#branch#enabled = 1

  let g:airline_powerline_fonts = 1
  let g:airline#extensions#tabline#enabled = 1
  let g:airline#extensions#tabline#left_sep = ' '
  let g:airline#extensions#tabline#left_alt_sep = '|'
  let g:airline#extensions#tabline#show_tabs = 1
  let g:airline#extensions#tabline#buffer_nr_show = 1
  let g:airline#extensions#whitespace#enabled = 0
  let g:airline#extensions#tabline#formatter = 'unique_tail'

endif

if dein#tap('switch.vim')

let g:switch_mapping = ""
nnoremap <silent> ts :Switch<cr>
let g:switch_custom_definitions =
  \ [
  \   ['&', '|'],
  \   ['~', '!'],
  \   ['always_ff', 'always_latch', 'always_comb'],
  \   ['posedge', 'negedge'],
  \   ['logic', 'bit'],
  \   ['@', 'wait'],
  \   [' <=', ' ='],
  \   ['input', 'output', 'ref'],
  \   ["'b", "'h", "'d"],
  \   ['endfunction', 'endtask', 'endclass', 'endinterface', 'endmodule', 'end', 'endclocking'],
  \   ['function', 'task'],
  \   ['WRITE', 'READ'],
  \ ]

endif

if dein#tap('vim-gutentags')

" set statusline+=%{gutentags#statusline()}
" set the file name suffix of tags file
let g:gutentags_enabled = 1
let g:gutentags_ctags_tagfile = '.tags'
let g:gutentags_project_root = ['.project', '.root', '.gitignore']
let g:gutentags_add_default_project_roots = 1
let g:gutentags_ctags_executable = 'C:/disk_1/ctags/ctags.exe'

" set the directory of the tags file
" let s:vim_tags = expand('./tags')
" if !isdirectory(s:vim_tags)
"   silent! call mkdir(s:vim_tags, 'p')
" endif
" let g:gutentags_cache_dir = s:vim_tags
" ctages arguments
let g:gutentags_ctags_extra_args = ['--extras=+q', '--fileds=+i', '-n']

endif

if dein#tap('asynctasks.vim')
" F4 to run AsyncTask [runTask]
nnoremap <silent><f4> :AsyncTask runTask<cr>
let g:asynctasks_rtp_config = "global_tasks.ini"
endif

if dein#tap('asyncrun.vim')
let g:asyncrun_open = 15
let g:asyncrun_rootmarks = ['.git', '.svn', '.root', '.project', '.hg']
let g:asynctasks_term_pos = 'external'


" 设置 F10 打开/关闭 Quickfix 窗口
nnoremap <silent> <F10> :call asyncrun#quickfix_toggle(15)<cr>

" F9 编译 C/C++ 文件
" nnoremap <silent> <F9> :AsyncRun gcc -Wall -O2 "$(VIM_FILEPATH)" -o "$(VIM_FILEDIR)/$(VIM_FILENOEXT)" <cr>

" F5 运行文件或者运行选中行的python代码
" nnoremap <silent> <F5> :AsyncTask runfile<cr>
nnoremap <silent> <F5> :call ExecuteFile()<cr>
vnoremap <silent> <F5> :AsyncRun -raw python<cr>

" F7 编译项目
" nnoremap <silent> <F7> :AsyncRun -cwd=<root> make <cr>

" F8 运行项目
" nnoremap <silent> <F8> :AsyncRun -cwd=<root> -raw make run <cr>

" F6 测试项目
" nnoremap <silent> <F6> :AsyncRun -cwd=<root> -raw make test <cr>

" 更新 cmake
" nnoremap <silent> <F4> :AsyncRun -cwd=<root> cmake . <cr>

" Windows 下支持直接打开新 cmd 窗口运行
" if has('win32') || has('win64')
"     nnoremap <silent> <F8> :AsyncRun -cwd=<root> -mode=4 make run <cr>
" endif


"----------------------------------------------------------------------
" F5 运行当前文件：根据文件类型判断方法，并且输出到 quickfix 窗口
"----------------------------------------------------------------------
function! ExecuteFile()
    let cmd = ''
    if index(['c', 'cpp', 'rs', 'go'], &ft) >= 0
        " native 语言，把当前文件名去掉扩展名后作为可执行运行
        " 写全路径名是因为后面 -cwd=? 会改变运行时的当前路径，所以写全路径
        " 加双引号是为了避免路径中包含空格
        let cmd = '"$(VIM_FILEDIR)/$(VIM_FILENOEXT)"'
    elseif &ft == 'python'
        let $PYTHONUNBUFFERED=1 " 关闭 python 缓存，实时看到输出
        let cmd = 'conda activate study && python "$(VIM_FILEPATH)"'
    elseif &ft == 'javascript'
        let cmd = 'node "$(VIM_FILEPATH)"'
    elseif &ft == 'perl'
        let cmd = 'perl "$(VIM_FILEPATH)"'
    elseif &ft == 'ruby'
        let cmd = 'ruby "$(VIM_FILEPATH)"'
    elseif &ft == 'php'
        let cmd = 'php "$(VIM_FILEPATH)"'
    elseif &ft == 'lua'
        let cmd = 'lua "$(VIM_FILEPATH)"'
    elseif &ft == 'zsh'
        let cmd = 'zsh "$(VIM_FILEPATH)"'
    elseif &ft == 'ps1'
        let cmd = 'powershell -file "$(VIM_FILEPATH)"'
    elseif &ft == 'vbs'
        let cmd = 'cscript -nologo "$(VIM_FILEPATH)"'
    elseif &ft == 'sh'
        let cmd = 'bash "$(VIM_FILEPATH)"'
    elseif &ft == 'go'
        let cmd = 'go run "$(VIM_FILEPATH)"'
    elseif &ft == 'markdown'
        exec 'MarkdownPreviewToggle'
        return
    else
        echo "unsupported language: " . &ft
        return
    endif
    " Windows 下打开新的窗口 (-mode=4) 运行程序，其他系统在 quickfix 运行
    " -raw: 输出内容直接显示到 quickfix window 不匹配 errorformat
    " -save=2: 保存所有改动过的文件
    " -cwd=$(VIM_FILEDIR): 运行初始化目录为文件所在目录
    if has('win32') || has('win64')
        " exec 'AsyncRun -cwd=$(VIM_FILEDIR) -raw -save=2 -mode=term -pos=floaterm -focus=0'. cmd
        exec 'AsyncRun -cwd=$(VIM_FILEDIR) -raw -save=2 -mode=async '. cmd
    else
        exec 'AsyncRun -cwd=$(VIM_FILEDIR) -raw -save=2 -mode=async '. cmd
    endif
endfunc

endif

if dein#tap('vim-visual-multi')

let g:VM_maps = {}
let g:VM_maps['Add Cursor Down'] = '<c-j>'
let g:VM_maps['Add Cursor Up'] = '<c-k>'

endif

if dein#tap('vista.vim')

let g:vista_sidebar_width = 40
let g:vista_cursor_delay = 100
let g:vista_echo_cursor_strategy = "floating_win"
let g:vista_update_on_text_changed = 0
let g:vista_stay_on_open = 1
let g:vista_blink = [1,0]
let g:vista_default_executive = 'ctags'
let g:vista_executive_for = {
  \ 'python': 'coc',
  \ }

nnoremap <silent> <leader>v :Vista!!<cr>

endif

if dein#tap('markdown-preview.nvim')

" ********************************************************************************
" settings of the markdown-preview.nvim
" ********************************************************************************

" set to 1, nvim will open the preview window after entering the markdown buffer
" default: 0
let g:mkdp_auto_start = 0

" set to 1, the nvim will auto close current preview window when change
" from markdown buffer to another buffer
" default: 1
let g:mkdp_auto_close = 1

" set to 1, the vim will refresh markdown when save the buffer or
" leave from insert mode, default 0 is auto refresh markdown as you edit or
" move the cursor
" default: 0
let g:mkdp_refresh_slow = 0

" set to 1, the MarkdownPreview command can be use for all files,
" by default it can be use in markdown file
" default: 0
let g:mkdp_command_for_global = 0

" set to 1, preview server available to others in your network
" by default, the server listens on localhost (127.0.0.1)
" default: 0
let g:mkdp_open_to_the_world = 0

" use custom IP to open preview page
" useful when you work in remote vim and preview on local browser
" more detail see: https://github.com/iamcco/markdown-preview.nvim/pull/9
" default empty
let g:mkdp_open_ip = ''

" specify browser to open preview page
" default: ''
let g:mkdp_browser = ''

" set to 1, echo preview page url in command line when open preview page
" default is 0
let g:mkdp_echo_preview_url = 0

" a custom vim function name to open preview page
" this function will receive url as param
" default is empty
let g:mkdp_browserfunc = ''

" options for markdown render
" mkit: markdown-it options for render
" katex: katex options for math
" uml: markdown-it-plantuml options
" maid: mermaid options
" disable_sync_scroll: if disable sync scroll, default 0
" sync_scroll_type: 'middle', 'top' or 'relative', default value is 'middle'
"   middle: mean the cursor position alway show at the middle of the preview page
"   top: mean the vim top viewport alway show at the top of the preview page
"   relative: mean the cursor position alway show at the relative positon of the preview page
" hide_yaml_meta: if hide yaml metadata, default is 1
" sequence_diagrams: js-sequence-diagrams options
" content_editable: if enable content editable for preview page, default: v:false
" disable_filename: if disable filename header for preview page, default: 0
let g:mkdp_preview_options = {
    \ 'mkit': {},
    \ 'katex': {},
    \ 'uml': {},
    \ 'maid': {},
    \ 'disable_sync_scroll': 0,
    \ 'sync_scroll_type': 'middle',
    \ 'hide_yaml_meta': 1,
    \ 'sequence_diagrams': {},
    \ 'flowchart_diagrams': {},
    \ 'content_editable': v:false,
    \ 'disable_filename': 0
    \ }


" set key blinding to toggle preview
nnoremap <leader>m :MarkdownPreviewToggle<cr>

" use a custom markdown style must be absolute path
" like '/Users/username/markdown.css' or expand('~/markdown.css')
let g:mkdp_markdown_css = ''

" use a custom highlight style must absolute path
" like '/Users/username/highlight.css' or expand('~/highlight.css')
let g:mkdp_highlight_css = ''

" use a custom port to start server or random for empty
let g:mkdp_port = ''

" preview page title
" ${name} will be replace with the file name
let g:mkdp_page_title = '「${name}」'

" recognized filetypes
" these filetypes will have MarkdownPreview... commands
let g:mkdp_filetypes = ['markdown']

endif

if dein#tap('vim-table-mode')

" ********************************************************************************
" key bindings of the vim-table-mode
" ********************************************************************************
let g:table_mode_tableize_map = '<Leader>tb'
let g:table_mode_tableize_d_map = '<Leader>T'
" for markdown table
let g:table_mode_corner='|'
augroup markdown_tablemode
  autocmd!
  autocmd FileType markdown exec "TableModeEnable"
augroup END

endif

if dein#tap('vim-floaterm')

" ********************************************************************************
" settings of the floaterm positon
" ********************************************************************************


let g:floaterm_position = 'bottom'

" if you are using on-demand loading feature provided by some plugin-managers,
" the keymap below won't take effect
" you have to define the key binding by yourself

" let g:floaterm_keymap_toggle = '<m-=>'
" let g:floaterm_keymap_new =
" let g:floaterm_keymap_prev =
" let g:floaterm_kgymap_next =
" let g:floaterm_keymap_first =
" let g:floaterm_keymap_last =
" let g:floaterm_keymap_show =
" let g:floaterm_keymap_kill =
" let g:floaterm_keymap_hide =

" key blindings of the vim-floaterm

nnoremap <silent> <m-+> :FloatermNew<CR>
tnoremap <silent> <m-+> <C-\><C-n>:FloatermNew<CR>
nnoremap <silent> <m-=> :FloatermToggle<CR>
tnoremap <silent> <m-=> <C-\><C-n>:FloatermToggle<CR>
nnoremap <silent> <m--> :FloatermKill<CR>
tnoremap <silent> <m--> <C-\><C-n>:FloatermKill<CR>
nnoremap <silent> <m-f> :FloatermNew fzf<cr>
nnoremap <silent> <m-r> :FloatermNew rg<cr>

endif

if dein#tap('indentLine')

  " let g:indentLine_enabled = 0
  let g:indentLine_concealcursor = 'nc'
  " indentLine will overwrite 'conceal' color with grey by default.
  " If you want to highlight conceal color with your colorscheme, disable by:
  let g:indentLine_setColors = 0
  let g:indentLine_fileTypeExclude = ['vista', 'coc-explorer', 'help']
endif

if dein#tap('far.vim')
  let g:far#enable_undo=1
endif

if dein#tap('bullets.vim')
  let g:bullets_enabled_file_types = [
  \ 'markdown',
  \ 'text',
  \ 'gitcommit',
  \ 'scratch'
  \]

  let g:bullets_enable_in_empty_buffers = 0
  let g:bullets_set_mappings = 0
  let g:bullets_line_spacing = 2
endif

if dein#tap('semshi') && dein#tap('vim-illuminate')
  function MyCustomHighLights()
    highlight semshiBuiltin ctermfg=87 guifg=#5fffff
    highlight semshiSelected ctermfg=231 guifg=#ffffff ctermbg=33 guibg=#0087ff
    highlight semshiImported ctermfg=167 guifg=#ffff87 cterm=bold gui=bold
  endfunction
  augroup python_highlight
    autocmd!
    autocmd FileType python call MyCustomHighLights()
  augroup END
endif

if dein#tap('vim-illuminate')

  if dein#tap('semshi')
    let g:Illuminate_ftblacklist = ['python']
  endif

  let g:Illuminate_ftblacklist += ['help', 'qf', 'far', 'leaderf', 'vista', 'floaterm', 'markdown']

endif
