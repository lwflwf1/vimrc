" Description:   The Plugin settings of vim configuration
" Maintainer:    lwflwf1
" Website:       https://github.com/lwflwf1/vimrc
" Created Time:  2021-04-21 16:55:35
" Last Modified: 2022-01-01 16:27:26
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
command! -nargs=0 DeinCheckClean call <SID>dein_check_clean()
command! -nargs=0 DeinList       call <SID>dein_list()

function s:dein_check_clean() abort
  if empty(dein#check_clean()) | echomsg 'No unused plugin' | return '' | endif
  echomsg 'Unused plugins:'
  for plugin in dein#check_clean()
    echomsg fnamemodify(plugin, ':t')
  endfor
endfunction

function s:dein_list() abort
  echomsg '[dein] S: sourced; X: not installed'
  let l:plugins = dein#get()
  echomsg 'Total plugins: '.len(l:plugins)
  for [name, plugin] in items(l:plugins)
    let prefix = ' '
    if !isdirectory(plugin.path)
      let prefix = 'X'
    elseif plugin.sourced
      let prefix = 'S'
    endif
    echomsg prefix name
  endfor
endfunction

" Disable vim distribution plugins
" let g:loaded_gzip = 1
" let g:loaded_tar = 1
" let g:loaded_tarPlugin = 1
" let g:loaded_zip = 1
" let g:loaded_zipPlugin = 1

" let g:loaded_getscript = 1
" let g:loaded_getscriptPlugin = 1
" let g:loaded_vimball = 1
" let g:loaded_vimballPlugin = 1

" " let g:loaded_matchit = 1
" " let g:loaded_matchparen = 1
" let g:loaded_2html_plugin = 1
" let g:loaded_logiPat = 1
" let g:loaded_rrhelper = 1

" let g:loaded_netrw = 1
" let g:loaded_netrwPlugin = 1
" let g:loaded_netrwSettings = 1
" let g:loaded_netrwFileHandlers = 1
" let g:loaded_netrwPlugin = 1

if dein#load_state(g:dein_dir)
call dein#begin(g:dein_dir)

call dein#add(s:dein_path)
call dein#add('ajmwagar/vim-deus')
call dein#add( 'joshdick/onedark.vim')
" call dein#add('romgrk/doom-one.vim')
call dein#add( 'ryanoasis/vim-devicons')
call dein#add('kyazdani42/nvim-web-devicons', {
  \ 'if': 'has("nvim")',
  \ })
call dein#add('itchyny/lightline.vim')
call dein#add('akinsho/bufferline.nvim', {
  \ 'if': 'has("nvim-0.5")',
  \ })
call dein#add('mengelbrecht/lightline-bufferline', {
  \ 'if': '!has("nvim-0.5")',
  \ })
" call dein#add('romgrk/barbar.nvim')
" call dein#add('theniceboy/eleline.vim')
" call dein#add('glepnir/spaceline.vim')
" call dein#add('liuchengxu/eleline.vim')
" call dein#add('bagrat/vim-buffet')
call dein#add( 'tpope/vim-repeat')
call dein#add( 'mzlogin/vim-markdown-toc')
call dein#add( 'yianwillis/vimcdoc')

" coc.nvim requires node 10.12+
call dein#add( 'neoclide/coc.nvim', {
  \ 'if': "has('nvim-0.3.2') || has('patch-8.0.1453')",
  \ 'rev': 'release',
  \ 'lazy': 1,
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

" call dein#add( 'Yggdroot/indentLine', {
"   \ 'lazy': 1,
"   \ 'on_event': 'BufReadPre'
"   \ })

call dein#add( 'vhda/verilog_systemverilog.vim', {
  \ 'lazy': 1,
  \ 'on_event': 'BufReadPre'
  \ })

call dein#add( 'ludovicchabant/vim-gutentags', {
  \ 'if': 'executable("ctags")',
  \ 'lazy':1,
  \ 'on_event': 'BufReadPost'
  \ })

" call dein#add( 'gcmt/wildfire.vim', {
"   \ 'lazy': 1,
"   \ 'on_map': '<Plug>(wildfire-'
"   \ })

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
  \ 'lazy': 1,
  \ 'on_cmd': ['AsyncTask', 'AsyncTaskList', 'AsyncTaskEdit'],
  \ 'on_source': 'asyncrun.vim'
  \ })

call dein#add( 'skywind3000/asyncrun.extra', {
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

call dein#add('lwflwf1/vim-session-manager', {
  \ 'lazy': 1,
  \ 'on_cmd': ['SessionList', 'SessionSave', 'SessionLoad']
  \ })

call dein#add('lwflwf1/vim-smart-hlsearch', {
  \ 'lazy': 1,
  \ 'on_map': ['n', 'N', '*', '#', 'g*', 'g#', '/', '?']
  \ })

call dein#add('vim-ruby/vim-ruby', {
  \ 'lazy': 1,
  \ 'on_ft': 'ruby',
  \ })

call dein#add('jiangmiao/auto-pairs')

call dein#add('rhysd/clever-f.vim')

call dein#add('vimwiki/vimwiki', {
  \ 'lazy': 1,
  \ 'on_ft': 'vimwiki',
  \ })

call dein#add('kristijanhusak/orgmode.nvim', {
  \ 'if': 'has("nvim-0.5")',
  \ })

" call dein#add('nvim-lua/plenary.nvim', {
"   \ 'if': 'has("nvim")',
"   \ })

" call dein#add('lewis6991/gitsigns.nvim', {
"   \ 'if': 'has("nvim-0.5")',
"   \ 'depends': 'plenary.nvim',
"   \ })

" call dein#add('itchyny/calendar.vim', {
"   \ 'lazy': 1,
"   \ 'on_cmd': 'Calendar',
"   \ })

" call dein#add('wlemuel/vim-tldr')

" call dein#add( 'justinmk/vim-sneak', {
"   \ 'lazy': 1,
"   \ 'on_map': '<Plug>Sneak'
"   \ })

" call dein#add('haya14busa/incsearch.vim')
" call dein#add('kana/vim-textobj-user')
" call dein#add('skywind3000/vim-terminal-help')
" call dein#add('skywind3000/vim-auto-popmenu')
" call dein#add('Linfee/ultisnips-zh-doc')
" call dein#add('SirVer/ultisnips')

call dein#end()
call dein#save_state()
endif
if dein#check_install()
  call dein#install()
endif
unlet s:dein_path

" lazy load coc.nvim
call timer_start(100, { -> dein#source('coc.nvim')})

" if !exists("g:plugs")
"     " mode, buffer number, file path, preview window flag,
"     " modified flag, read only flag
"     set statusline=\ %{functions#GetMode()}\ \|\ [%n]\ %F\ %w\ %m\ %r
"     if exists('g:loaded_vim_session_manager')
"         set statusline+=\ %{SessionStatusLine()}
"     endif
"     set statusline+=%=
"     " filetype, percentage, line number, total line numbers, column number
"     set statusline+=%y\ %p%%\ ???\ %l/%L\ ???:%c
" endif
"

if dein#tap('vim-tldr')
  let g:tldr_directory_path = g:data_dir.'tldr'
  if !isdirectory('g:tldr_directory_path')
    silent! call mkdir(g:tldr_directory_path, 'p')
  endif
  let g:tldr_language = 'zh'
  if g:os == 'windows'
    let g:tldr_enabled_categories = ["windows", "common"]
  elseif g:os == 'unix'
    let g:tldr_enabled_categories = ["linux", "common"]
  else
    let g:tldr_enabled_categories = ["osx", "common"]
  endif
endif

if dein#tap('bufferline.nvim')
  lua require("bufferline").setup{
    \ options = {
      \ numbers = "none",
      \ offsets = {{filetype = "coc-explorer", text = "File Explorer", highlight = "Directory"}},
      \ diagnostics = "coc",
      \ diagnostics_indicator = function(count, level, diagnostics_dict, context)
      \   local icon = level:match("error") and "??? " or "??? "
      \   return " " .. icon .. count
      \ end
    \}
  \}
  " \ mappings = false,
  " \ number_style = "none",
  nnoremap <silent> <leader>bn :BufferLineMoveNext<cr>
  nnoremap <silent> <leader>bp :BufferLineMovePrev<cr>
  nnoremap <silent> <leader>bb :BufferLinePick<cr>
  nnoremap <silent> <leader>bl :BufferLineCloseLeft<cr>
  nnoremap <silent> <leader>br :BufferLineCloceRight<cr>
  nnoremap <silent> <leader>bd :BufferLineSortByDirectory<cr>
  nnoremap <silent> <leader>be :BufferLineSortByExtension<cr>
  nnoremap <silent> <leader>bt :BufferLineSortByTabs<cr>

  nnoremap <silent> <leader>1 :BufferLineGoToBuffer 1<cr>
  nnoremap <silent> <leader>2 :BufferLineGoToBuffer 2<cr>
  nnoremap <silent> <leader>3 :BufferLineGoToBuffer 3<cr>
  nnoremap <silent> <leader>4 :BufferLineGoToBuffer 4<cr>
  nnoremap <silent> <leader>5 :BufferLineGoToBuffer 5<cr>
  nnoremap <silent> <leader>6 :BufferLineGoToBuffer 6<cr>
  nnoremap <silent> <leader>7 :BufferLineGoToBuffer 7<cr>
  nnoremap <silent> <leader>8 :BufferLineGoToBuffer 8<cr>
  nnoremap <silent> <leader>9 :BufferLineGoToBuffer 9<cr>
endif

if dein#tap('orgmode.nvim')
  let g:org_dir = g:data_dir.'org'
  if !isdirectory('g:tldr_directory_path')
    silent! call mkdir(g:tldr_directory_path, 'p')
  endif
  execute "lua require('orgmode').setup({
    \ org_agenda_files = '".escape(g:org_dir, ' \')."/*',
    \ org_default_notes_file = '".escape(g:org_dir, ' \')."/refile.org',
    \ org_todo_keywords = {'TODO(t)', 'DOING(i)', 'SUSPEND(s)', '|', 'DONE(d)', 'CANCELED(c)'},
    \ org_todo_keyword_faces = {
      \ DOING    = ':foreground #7fff00',
      \ SUSPEND  = ':foreground orchid',
      \ CANCELED = ':foreground gold'
    \ },
    \ org_hide_leading_stars            = true,
    \ org_hide_emphasis_markers         = true,
    \ org_agenda_span                   = 'day',
    \ org_agenda_skip_deadline_if_done  = true,
    \ org_agenda_skip_scheduled_if_done = true,
    \ mappings = {
      \ org = {
        \ org_forward_heading_same_level          = ']',
        \ org_backward_heading_same_level         = '[',
        \ org_move_subtree_down                   = '<leader>oj',
        \ org_move_subtree_up                     = '<leader>ok',
        \ org_insert_todo_heading_respect_content = '<leader>ot',
        \ org_insert_todo_heading                 = '<leader>oT',
        \ org_insert_heading_respect_content      = '<leader>oh',
        \ org_meta_return                         = '<m-cr>',
        \ org_set_tags_command                    = '<leader>og',
        \ org_open_at_point                       = '<cr>',
      \}
    \}
    \})"
endif

if dein#tap('clever-f.vim')
  let g:clever_f_ignore_case = 1
endif

if dein#tap('auto-pairs')
  let g:AutoPairFlyMode = 0
  let g:AutoPairShortBackInsert = ''
endif

if dein#tap('vim-session-manager')
  let g:session_default_session_enable = 0
  nnoremap <silent> <leader>L :SessionList<cr>
  nnoremap <silent> <leader>S :SessionSave<cr>
  nnoremap <silent> <leader>R :SessionLoad<cr>
endif

if dein#tap('wildfire.vim')
  map <cr> <Plug>(wildfire-fuel)
  nmap <c-cr> <Plug>(wildfire-quick-select)
endif

if dein#tap('lightline.vim')
  let s:special_filetypes = ['coc-explorer', 'vista', 'sessionlist', 'help', 'fugitive', 'qf', 'floaterm']
  let s:lightline_nerd_font_enable = 1
  let s:nerd_font_icons = {
    \ 'modified'    : "???",
    \ 'readonly'    : "\uf456",
    \ 'session'     : "\uf413",
    \ 'git'         : "\ue725",
    \ 'gitadd'      : "+",
    \ 'gitdelete'   : "-",
    \ 'gitmodified' : "~",
    \ 'error'       : "\uf467",
    \ 'warning'     : "\uf071",
    \ }
    " \ 'modified'    : "\uf040",
    " \ 'gitadd'      : "\uf457",
    " \ 'gitdelete'   : "\uf458",
    " \ 'gitmodified' : "\uf459",
  let s:normal_icons = {
    \ 'modified'    : "+",
    \ 'readonly'    : "RO",
    \ 'session'     : "S:",
    \ 'git'         : "Git:",
    \ 'gitadd'      : "+",
    \ 'gitdelete'   : "-",
    \ 'gitmodified' : "~",
    \ 'error'       : "X",
    \ 'warning'     : "!",
    \ }
  if s:lightline_nerd_font_enable ==# 1
    let s:icons = s:nerd_font_icons
  else
    let s:icons = s:normal_icons
  endif

  function Gitinfo() abort
    if index(s:special_filetypes, &ft) !=# -1 | return '' | endif
    let l:gitname = ''
    let l:gitsummary = []
    if exists('g:loaded_gitgutter') | let l:gitsummary = GitGutterGetHunkSummary() | endif
    if exists('g:loaded_fugitive') | let l:gitname = FugitiveHead() | endif
    if empty(l:gitname)
      return ''
    elseif empty(l:gitsummary)
      return s:icons['git'].' '.l:gitname
    elseif winwidth(0) > 100
      return join([s:icons['git'], l:gitname, s:icons['gitadd'].l:gitsummary[0], s:icons['gitmodified'].l:gitsummary[1], s:icons['gitdelete'].l:gitsummary[2]], ' ')
    else
      return join([s:icons['gitadd'].l:gitsummary[0], s:icons['gitmodified'].l:gitsummary[1], s:icons['gitdelete'].l:gitsummary[2]], ' ')
    endif
  endfunction

  function MyLightlineFileType() abort
    return index(s:special_filetypes, &ft) !=# -1 || &ft ==# '' || winwidth(0) < 90 ? '' : &ft
  endfunction

  function MyLightlineReadonly() abort
    if index(s:special_filetypes, &ft) !=# -1 || !&readonly && &modifiable | return '' | endif
    return s:icons['readonly']
  endfunction

  function MyLightlineMode() abort
    return index(s:special_filetypes, &ft) !=# -1 ?  &ft : lightline#mode()
  endfunction

  function MyLightlineFilename() abort
    if index(s:special_filetypes, &ft) !=# -1 | return '' | endif
    let l:filename = trim(WebDevIconsGetFileTypeSymbol()." ".expand('%:t'))
    let l:modified = &modified ? ' '.s:icons['modified']: ''
    return l:filename.l:modified
  endfunction

  function MyLightlineSession() abort
    if exists('g:loaded_vim_session_manager') && winwidth(0) > 80 && !empty(SessionStatusLine())
      return s:icons['session'].' '.SessionStatusLine()
    endif
    return ''
  endfunction

  function MyLightlineFileformat() abort
    if index(s:special_filetypes, &ft) !=# -1 || winwidth(0) < 120 | return '' | endif
    return &fileformat
  endfunction

  function MyLightlineFileencoding() abort
    if index(s:special_filetypes, &ft) !=# -1 || winwidth(0) < 110 | return '' | endif
    return &fileencoding
  endfunction

  function MyLightlineVista() abort
    if index(s:special_filetypes, &ft) !=# -1 || winwidth(0) < 70 | return '' | endif
    let l:nearest_function = get(b:, 'vista_nearest_method_or_function', '')
    if !empty(nearest_function)
      return "\uf794 ".l:nearest_function
    else
      return ''
    endif
  endfunction

  function MyLightlineInactiveMode() abort
    if index(s:special_filetypes, &ft) !=# -1 | return &ft | endif
    return expand('%:t')
  endfunction

  function! MyLightlineCocStatus()
    if index(s:special_filetypes, &ft) !=# -1 | return '' | endif
    let info = get(b:, 'coc_diagnostic_info', {})
    let msgs = []
    " if get(info, 'error', 0)
    call add(msgs, s:icons['error'].' '.get(info, 'error', 0))
    " endif
    " if get(info, 'warning', 0)
    call add(msgs, s:icons['warning'].' '.get(info, 'warning', 0))
    " endif
    " return trim(join(msgs, ' ') . ' ' . get(g:, 'coc_status', ''))
    return join(msgs, ' ')
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
    \   'vista'        : 'MyLightlineVista',
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
    \ 'right': [['lineinfo'],
    \           ['percent'],
    \           ['vista', 'spell', 'filetype', 'fileencoding', 'fileformat']]
    \ }

  let g:lightline.inactive = {
    \ 'left': [['inactivemode']],
    \ 'right': [['lineinfo'],
    \           ['percent']],
    \ }
endif

if dein#tap('lightline-bufferline')
    let g:lightline#bufferline#enable_devicons = 1
    let g:lightline#bufferline#show_number = 4
    let g:lightline#bufferline#read_only = ' '.s:icons['readonly']
    let g:lightline#bufferline#modified = ' '.s:icons['modified']
    let g:lightline#bufferline#clickable = 1
    let g:lightline.component_raw = {'buffers': 1}
    let g:lightline#bufferline#ordinal_separator = '|'
    " let g:lightline#bufferline#unicode_symbols = 1
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
  map ;j <Plug>(easymotion-j)
  map ;k <Plug>(easymotion-k)
  map ;s <Plug>(easymotion-s)
  map ;w <Plug>(easymotion-w)
  map ;e <Plug>(easymotion-e)
  map ;b <Plug>(easymotion-b)
  map ;W <Plug>(easymotion-W)
  map ;E <Plug>(easymotion-E)
  map ;B <Plug>(easymotion-B)
  map ;J <Plug>(easymotion-eol-j)
  map ;K <Plug>(easymotion-eol-k)
  map ;l <Plug>(easymotion-jumptoanywhere)
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

" if dein#tap('incsearch.vim')
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
" endif

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
  let g:UltiSnipsExpandTrigger      = "<m-e>"
  let g:UltiSnipsJumpForwardTrigger = "<m-e>"
  let g:UltiSnipsSnippetDir         = g:data_dir.'Ultisnips'
  let g:UltiSnipsSnippetDirectories = [g:data_dir.'Ultisnips']
  let g:UltiSnipsEditSplit          = "vertical"
endif

if dein#tap('coc.nvim')
  if has('nvim-0.4.0') || has('patch-8.2.0750')
    nnoremap <silent><nowait><expr> <C-d> coc#float#has_scroll() ? coc#float#scroll(1) : "\<C-d>zz"
    nnoremap <silent><nowait><expr> <C-u> coc#float#has_scroll() ? coc#float#scroll(0) : "\<C-u>zz"
    inoremap <silent><nowait><expr> <C-d> coc#float#has_scroll() ? "\<c-r>=coc#float#scroll(1)\<cr>" : "\<del>"
    inoremap <silent><nowait><expr> <C-u> coc#float#has_scroll() ? "\<c-r>=coc#float#scroll(0)\<cr>" : "\<c-u>"
    vnoremap <silent><nowait><expr> <C-d> coc#float#has_scroll() ? coc#float#scroll(1) : "\<C-d>zz"
    vnoremap <silent><nowait><expr> <C-u> coc#float#has_scroll() ? coc#float#scroll(0) : "\<C-u>zz"
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

nnoremap <silent> <leader>e :CocCommand explorer<CR>

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

nnoremap <silent> <leader>cs :set operatorfunc=<sid>cocsearch<cr>g@
vnoremap <silent> <leader>cs :<c-u>call <sid>cocsearch(visualmode())<cr>

function s:cocsearch(type) abort
  let l:reg_save = @"
  if a:type ==# 'char'
    execute "normal! `[v`]y"
    execute "CocSearch -F ".escape(@", ' \/')
  elseif a:type ==# 'v'
    execute "normal! `<v`>y"
    execute "CocSearch -F ".escape(@", ' \/')
  endif
  let @" = l:reg_save
endfunction

" Applying codeAction to the selected region.
" Example: `<leader>cap` for current paragraph
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

let g:coc_global_extensions = [
  \ 'coc-json',
  \ 'coc-vimlsp',
  \ 'coc-pyright',
  \ 'coc-highlight',
  \ 'coc-sh',
  \ 'coc-lists',
  \ 'coc-yank',
  \ 'coc-translator',
  \ 'coc-snippets',
  \ 'coc-tabnine',
  \ 'coc-tasks',
  \ 'coc-marketplace',
  \ 'coc-yaml',
  \ 'coc-solargraph',
  \ ]

  if has('nvim-0.3.1') || has('patch-8.1.1418')
    let g:coc_global_extensions += ['coc-explorer']
  endif

  if executable('clangd')
    let g:coc_global_extensions += ['coc-clangd']
  endif

endif

if dein#tap('vim-gitgutter')

let g:gigutter_enable = 1
let g:gitgutter_highlight_lines = 0
let g:gitgutter_highlight_linenrs = 1
let g:gitgutter_map_keys = 0
let g:gitgutter_max_signs = 500
let g:gitgutter_preview_win_floating = 1
" let g:gitgutter_git_executable = 'C:\disk_1\Git\bin\git.exe'

command! GitInQuickFix GitGutterQuickFix | copen

nnoremap <silent> <leader>gk :GitGutterPrevHunk<cr>
nnoremap <silent> <leader>gj :GitGutterNextHunk<cr>
nnoremap <silent> <leader>gh :GitGutterPreviewHunk<cr>
nnoremap <silent> <leader>gu :GitGutterUndoHunk<cr>
nnoremap <silent> <leader>gs :GitGutterStageHunk<cr>
nnoremap <silent> <leader>gq :GitInQuickFix<cr>
nnoremap <silent> <leader>gf :GitGutterFold<cr>
nnoremap <silent> <leader>ga :GitGutterAll<cr>
omap ih <Plug>(GitGutterTextObjectInnerPending)
omap ah <Plug>(GitGutterTextObjectOuterPending)
xmap ih <Plug>(GitGutterTextObjectInnerVisual)
xmap ah <Plug>(GitGutterTextObjectOuterVisual)

endif

if dein#tap('vim-fugitive')

nnoremap <silent> <leader>gw :Gwrite<cr>
nnoremap <silent> <leader>gr :Gread<cr>
nnoremap <silent> <leader>gd :Gdiffsplit @<cr>
nnoremap <silent> <leader>gb :Git blame<cr>
nnoremap <silent> <leader>gg :Git<cr>
nnoremap <silent> <leader>gl :Git log<cr>
nnoremap <silent> <leader>gp :Git pull<cr>
nnoremap <silent> <leader>gP :Git push<cr>
nnoremap <silent> <leader>gc :Git commit<cr>
nnoremap <silent> <leader>gA :Git commit --amend --no-edit<cr>

endif

if dein#tap('vim-sneak')

map f <Plug>Sneak_s
map F <Plug>Sneak_S

endif

if dein#tap('LeaderF')
" let g:Lf_Ctags = 'C:/disk_1/ctags/ctags.exe'
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
  \ 'BufTag': 0,
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

let g:Lf_RgConfig = [
  \ "--hidden",
  \]

if executable('rg')
  let g:Lf_DefaultExternalTool = 'rg'
  let g:Lf_ExternalCommand = 'rg --files --no-ignore "%s"'
endif

let g:Lf_ShortcutF = ""
let g:Lf_ShortcutB = ""
nnoremap <leader>fF :LeaderfFile
nnoremap <silent> <leader>ff :LeaderfFile<cr>
nnoremap <silent> <leader>fm :LeaderfMru<CR>
nnoremap <silent> <leader>fu :LeaderfFunction<CR>
" nnoremap <silent> <F12> :call <SID>leaderfFunctionToggle()<CR>
nnoremap <silent> <leader>fl :LeaderfLine<CR>
nnoremap <silent> <leader>fL :LeaderfLineAll<CR>
nnoremap <silent> <leader>fw :Leaderf line --cword<CR>
nnoremap <silent> <leader>fr :Leaderf --recall<CR>
nnoremap <silent> <leader>ft :LeaderfBufTagAll<CR>
nnoremap <silent> <leader>fb :LeaderfBuffer<cr>
" nnoremap <silent> <leader>fs :Leaderf floaterm<cr>
nnoremap <silent> <leader>fc :LeaderfCommand<cr>
nnoremap <silent> <leader>fh :LeaderfHistoryCmd<cr>
nnoremap <silent> <leader>fq :LeaderfQuickFix<cr>
nnoremap <silent> <leader>fk :LeaderfMarks<cr>
" nnoremap <silent> <leader>rg :Leaderf rg<CR>
nnoremap <silent> <leader>rg :LeaderfRgInteractive<CR>
nmap <silent> <leader>rw <Plug>LeaderfRgCwordLiteralBoundary<cr>
nmap <silent> <leader>rW <Plug>LeaderfRgCwordLiteralNoBoundary<cr>
xmap <silent> <leader>rg <Plug>LeaderfRgVisualLiteralNoBoundary<cr>
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

if executable('ctags') | let g:gutentags_enabled = 1 | endif
let g:gutentags_ctags_tagfile = '.tags'
let g:gutentags_project_root = ['.project', '.root', '.gitignore']
let g:gutentags_add_default_project_roots = 1
let g:gutentags_generate_on_write = 1
let g:gutentags_file_list_command = {
    \ 'markers': {
      \ '.git': 'git ls-files',
      \ '.hg': 'hg files',
      \ },
    \ }

" let g:gutentags_ctags_executable = 'C:/disk_1/ctags/ctags.exe'

" set the directory of the tags file
if has('nvim')
  let s:tags_dir = stdpath('data').'/tags/'
else
  let s:tags_dir = $HOME.'/.vim/tags/'
endif
if !isdirectory(s:tags_dir)
  silent! call mkdir(s:tags_dir, 'p')
endif

let g:gutentags_cache_dir = s:tags_dir
" ctages arguments
let g:gutentags_ctags_extra_args = ['--extras=+q', '--fields=+i', '-n']

function s:list_tags() abort
  let l:tags = map(globpath(s:tags_dir, '*'.g:gutentags_ctags_tagfile, 1, 1), 'fnamemodify(v:val, ":t")')
  for t in l:tags
    echomsg t
  endfor
endfunction

function s:delete_tags(bang, ...) abort
  if a:bang
    let l:tags = globpath(s:tags_dir, '*'.g:gutentags_ctags_tagfile, 1, 1)
    for t in l:tags
      call delete(t)
    endfor
  elseif a:0 ==# 0
    echo 'You must specify tags to delete!'
  else
    for t in a:000
      call delete(s:tags_dir.t)
    endfor
  endif
endfunction

function s:delete_tags_complete(ArgLead, CmdLine, CursorPos) abort
  return join(map(globpath(s:tags_dir, '*'.g:gutentags_ctags_tagfile, 1, 1), 'fnamemodify(v:val, ":t")'), "\n")
endfunction

command! -nargs=0 GutentagsList call <sid>list_tags()
command! -nargs=* -bang -complete=custom,<sid>delete_tags_complete GutentagsDelete call <sid>delete_tags(<bang>0, <f-args>)

endif

if dein#tap('asynctasks.vim')
" F4 to run AsyncTask [runTask]
" nnoremap <silent><f4> :AsyncTask runTask<cr>
let g:asynctasks_rtp_config = "global_tasks.ini"
endif

if dein#tap('asyncrun.vim')
let g:asyncrun_open = 15
let g:asyncrun_rootmarks = ['.git', '.svn', '.root', '.project', '.hg']
let g:asynctasks_term_pos = 'external'


" ?????? F10 ??????/?????? Quickfix ??????
nnoremap <silent> <F10> :call asyncrun#quickfix_toggle(15)<cr>

" F9 ?????? C/C++ ??????
" nnoremap <silent> <F9> :AsyncRun gcc -Wall -O2 "$(VIM_FILEPATH)" -o "$(VIM_FILEDIR)/$(VIM_FILENOEXT)" <cr>
nnoremap <silent> <F9> :call <sid>compile_c()<cr>
function s:compile_c() abort
  if index(['c', 'cpp'], &ft) >= 0
    let l:cmd = 'gcc -Wall -O2 "$(VIM_FILEPATH)" -o "$(VIM_FILEDIR)/$(VIM_FILENOEXT)"'
    execute 'AsyncRun -cwd=$(VIM_FILEDIR) -save=2 -mode=async '.l:cmd
  else
    echo 'this is not a c(cpp) file!'
    return
  endif
endfunction

" F5 ????????????????????????????????????python??????
" nnoremap <silent> <F5> :AsyncTask runfile<cr>
nnoremap <silent> <F5> :call ExecuteFile()<cr>
vnoremap <silent> <F5> :AsyncRun -raw python<cr>

" F7 ????????????
" nnoremap <silent> <F7> :AsyncRun -cwd=<root> make <cr>

" F8 ????????????
" nnoremap <silent> <F8> :AsyncRun -cwd=<root> -raw make run <cr>

" F6 ????????????
" nnoremap <silent> <F6> :AsyncRun -cwd=<root> -raw make test <cr>

" ?????? cmake
" nnoremap <silent> <F4> :AsyncRun -cwd=<root> cmake . <cr>

" Windows ???????????????????????? cmd ????????????
" if has('win32') || has('win64')
"     nnoremap <silent> <F8> :AsyncRun -cwd=<root> -mode=4 make run <cr>
" endif


"----------------------------------------------------------------------
" F5 ????????????????????????????????????????????????????????????????????? quickfix ??????
"----------------------------------------------------------------------
function! ExecuteFile()
    let cmd = ''
    if index(['c', 'cpp', 'rs', 'go'], &ft) >= 0
        " native ??????????????????????????????????????????????????????????????????
        " ?????????????????????????????? -cwd=? ??????????????????????????????????????????????????????
        " ????????????????????????????????????????????????
        let cmd = '"$(VIM_FILEDIR)/$(VIM_FILENOEXT)"'
    elseif &ft == 'python'
        let $PYTHONUNBUFFERED=1 " ?????? python ???????????????????????????
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
    elseif &ft == 'vim'
        exec 'source '.expand('%')
        return
    elseif &ft == 'markdown'
        exec 'MarkdownPreviewToggle'
        return
    else
        echo "unsupported language: " . &ft
        return
    endif
    " Windows ????????????????????? (-mode=4) ?????????????????????????????? quickfix ??????
    " -raw: ??????????????????????????? quickfix window ????????? errorformat
    " -save=2: ??????????????????????????????
    " -cwd=$(VIM_FILEDIR): ??????????????????????????????????????????
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
  \ 'vim': 'coc',
  \ }

nnoremap <silent> <leader>V :Vista!!<cr>

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
let g:mkdp_page_title = '???${name}???'

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
nnoremap <silent> <c-g> :FloatermNew --title=lazygit --width=1.0 --height=1.0 lazygit<cr>

endif

if dein#tap('indentLine')

  " let g:indentLine_enabled = 0
  let g:indentLine_concealcursor = 'nc'
  " indentLine will overwrite 'conceal' color with grey by default.
  " If you want to highlight conceal color with your colorscheme, disable by:
  let g:indentLine_setColors = 0
  let g:indentLine_fileTypeExclude = [
    \ 'vista',
    \ 'coc-explorer',
    \ 'help',
    \ 'git',
    \ 'log',
    \ 'org',
    \ 'orgagenda',
    \ ]
  let g:indentLine_bufTypeExclude = [
    \ 'popup',
    \ ]
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
  " let g:bullets_set_mappings = 0
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

  let g:Illuminate_ftblacklist += [
    \ 'help',
    \ 'qf',
    \ 'far',
    \ 'leaderf',
    \ 'vista',
    \ 'floaterm',
    \ 'markdown',
    \ 'git',
    \ 'gitcommit',
    \ 'org',
    \ 'orgagenda'
    \]
endif

if dein#tap('verilog_systemverilog.vim')
  let g:verilog_navigate_split = "v"
  let g:verilog_indent_assign_fix = 1
  let g:verilog_syntax_fold_lst = "all"
  let g:verilog_efm_level = "warning"
  let g:verilog_efm_uvm_lst = "fatal,error,warning"
  " let g:verilog_efm_quickfix_clean = 1
  " let g:verilog_efm_custom = %t:\ %m

  nnoremap <leader>vi :VerilogFollowInstance<cr>
  nnoremap <leader>vp :VerilogFollowPort<cr>
  nnoremap <leader>vr :VerilogReturnInstance<cr>
  nnoremap <leader>vg :VerilogGotoInstanceStart<cr>
  nnoremap <leader>ve :VerilogErrorFormat vcs 1<cr>
endif

" let g:netrw_liststyle = 3
" let g:netrw_browse_split = 3

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
