--[==[
Quarto filter for running fortl code inside articles.

Cells are written as

  ```{.fortl}
  x : Float[Unit[m]] = 2.0
  ```

and are run cumulatively (like a notebook): each cell sees the
definitions of all earlier cells in the same `session` (default
"main"). Under each cell we show the type and value of the last
definition in that cell.

Cells can also show (part of) a file from the repository:

  ```{.fortl file="../examples/geotherm-inversion.frtl" lines="40-50"}
  ```

The whole file is run on its own and its `it` (or the binding named
by `show=`) is displayed; the excerpt links to the full file.

Cell attributes:
  eval=false      show the code but don't run it
  echo=false      run the code but hide it (only show the output)
  output=false    run the code but hide the output
  error=true      the cell is expected to fail (don't warn)
  show=name       display this binding instead of the last one
  session=name    run in a separate cumulative session
  file=path       take the code from a file (relative to the .qmd)
  lines=a-b       only display these lines of the file

Document metadata (all optional):
  fortl:
    command: fortl                    # path to the fortl executable
    repo-root: ..                     # repo root, relative to the .qmd
    repo-url: https://github.com/plas4sci/fortl/blob/main/
    simplify-types: true              # drop grade sets like [{UoM}]
]==]

local config = {
  command = "fortl",
  repo_root = nil,
  repo_url = nil,
  simplify_types = true,
}

-- session name -> list of source chunks
local sessions = {}

local function meta_string(v)
  if v == nil then return nil end
  return pandoc.utils.stringify(v)
end

local function input_dir()
  if quarto and quarto.doc and quarto.doc.input_file then
    return pandoc.path.directory(quarto.doc.input_file)
  end
  return "."
end

local function read_file(path)
  local fh = io.open(path, "r")
  if not fh then return nil end
  local s = fh:read("a")
  fh:close()
  return s
end

local function write_file(path, s)
  local fh = assert(io.open(path, "w"))
  fh:write(s)
  fh:close()
end

local function split_lines(s)
  local lines = {}
  for line in (s .. "\n"):gmatch("(.-)\r?\n") do
    table.insert(lines, line)
  end
  -- drop the trailing empty line produced by a final newline
  if #lines > 0 and lines[#lines] == "" then table.remove(lines) end
  return lines
end

local function count_lines(s)
  return #split_lines(s)
end

local function shell_quote(s)
  return "'" .. s:gsub("'", "'\\''") .. "'"
end

-- Name of the last top-level definition in a chunk of source, skipping
-- over docstrings (which may contain things that look like bindings).
local function last_binding(src)
  local name = nil
  local in_doc = false
  for _, line in ipairs(split_lines(src)) do
    local _, quotes = line:gsub('"""', "")
    if in_doc then
      if quotes % 2 == 1 then in_doc = false end
    elseif quotes % 2 == 1 then
      in_doc = true
    else
      local n = line:match("^([%a_][%w_']*)%s*:") or
                line:match("^([%a_][%w_']*)%s*=[^=]") or
                line:match("^([%a_][%w_']*)%s*=$")
      if n then name = n end
    end
  end
  return name
end

local function strip_ansi(s)
  return (s:gsub("\27%[[%d;]*m", ""))
end

local function simplify_type(t)
  if not config.simplify_types then return t end
  t = t:gsub("%[{[^}]*}%]", "")      -- grade sets, e.g. Float[{UoM}][...]
  t = t:gsub("(%^%-?%d+)%.0", "%1")  -- m^2.0 -> m^2
  return t
end

-- Run fortl on a file; returns { ok, type, value, message }.
-- `offset` lines are subtracted from line numbers in error messages
-- (and the file name replaced by `label`) so they refer to the cell.
local function run_fortl(path, offset, label)
  local cmd = shell_quote(config.command) .. " " .. shell_quote(path) .. " 2>&1"
  local proc = io.popen(cmd)
  local out = strip_ansi(proc:read("a"))
  local ok = proc:close()

  local lines = {}
  for _, line in ipairs(split_lines(out)) do
    if not (line:match("^fortl v") or line:match("^Checking ")) then
      table.insert(lines, line)
    end
  end

  local body = table.concat(lines, "\n")
  local ty, value = body:match("^Well%-typed as ([^\n]*)\n?(.*)$")
  if ok and ty then
    return { ok = true, type = simplify_type(ty), value = value }
  end

  -- Re-target error locations at the cell rather than the temp file
  local escaped = path:gsub("[%^%$%(%)%%%.%[%]%*%+%-%?]", "%%%0")
  body = body:gsub(escaped .. ":(%d+):(%d+)", function(l, c)
    local line = tonumber(l) - offset
    if line < 1 then
      return "(earlier cell):" .. l .. ":" .. c
    end
    return label .. ":" .. line .. ":" .. c
  end)
  body = body:gsub("^Not well%-typed%.\n?", "")
  body = body:gsub("^Error: ", "")
  return { ok = false, message = simplify_type(body) }
end

local function truthy(v, default)
  if v == nil then return default end
  return v == "true" or v == "yes" or v == "1"
end

-- Parse `#| key: value` option lines (Quarto style) off the top of a cell.
local function take_comment_options(text, attrs)
  local lines = split_lines(text)
  local i = 1
  while i <= #lines do
    local k, v = lines[i]:match("^#|%s*([%w%-_]+)%s*:%s*(.-)%s*$")
    if not k then break end
    attrs[k] = v:gsub('^"(.*)"$', "%1")
    i = i + 1
  end
  return table.concat(lines, "\n", i)
end

local function parse_range(s, max)
  if not s then return 1, max end
  local a, b = s:match("^(%d+)%s*%-%s*(%d+)$")
  if a then return tonumber(a), math.min(tonumber(b), max) end
  local n = s:match("^(%d+)$")
  if n then return tonumber(n), tonumber(n) end
  return 1, max
end

local function output_block(name, result, expect_error)
  if result.ok then
    local text = (name and (name .. " : ") or "") .. result.type
    if result.value and result.value ~= "" and result.value ~= "None" then
      text = text .. "\n" .. string.rep(" ", name and #name or 0) .. "= " .. result.value
    end
    return pandoc.Div(
      { pandoc.CodeBlock(text, pandoc.Attr("", { "fortl-result" })) },
      pandoc.Attr("", { "fortl-output", "fortl-ok" }))
  end
  return pandoc.Div(
    { pandoc.CodeBlock(result.message, pandoc.Attr("", { "fortl-result" })) },
    pandoc.Attr("", { "fortl-output", expect_error and "fortl-expected-error" or "fortl-error" }))
end

-- Header above a file excerpt, linking to the full file.
local function file_header(relpath, first, last, total)
  local target = relpath
  if config.repo_url then
    target = config.repo_url .. relpath
    if first ~= 1 or last ~= total then
      target = target .. "#L" .. first .. "-L" .. last
    end
  end
  local inlines = { pandoc.Link(pandoc.Code(relpath), target) }
  if first ~= 1 or last ~= total then
    table.insert(inlines, pandoc.Space())
    table.insert(inlines, pandoc.Emph(pandoc.Str(
      "(lines " .. first .. "–" .. last .. " of " .. total .. ")")))
  end
  return pandoc.Div({ pandoc.Plain(inlines) }, pandoc.Attr("", { "fortl-file" }))
end

local function is_fortl(el)
  return el.classes:includes("fortl") or el.classes:includes("{fortl}")
end

local function code_block(el)
  if not is_fortl(el) then return nil end

  local attrs = {}
  for k, v in pairs(el.attributes) do attrs[k] = v end
  local text = take_comment_options(el.text, attrs)

  local eval = truthy(attrs.eval, true)
  local echo = truthy(attrs.echo, true)
  local show_output = truthy(attrs.output, true)
  local expect_error = truthy(attrs.error, false)

  local blocks = {}
  local result, shown_name

  if attrs.file then
    local path = pandoc.path.join({ input_dir(), attrs.file })
    local src = read_file(path)
    if not src then
      quarto.log.error("fortl: cannot read file " .. attrs.file)
      return pandoc.Div({ pandoc.Para({ pandoc.Strong(pandoc.Str(
        "Missing file: " .. attrs.file)) }) }, pandoc.Attr("", { "fortl-error" }))
    end

    local all = split_lines(src)
    local first, last = parse_range(attrs.lines, #all)
    local relpath = attrs.file
    if config.repo_root then
      relpath = pandoc.path.make_relative(
        pandoc.path.normalize(pandoc.path.join({ input_dir(), attrs.file })),
        pandoc.path.normalize(pandoc.path.join({ input_dir(), config.repo_root })))
    end

    if echo then
      table.insert(blocks, file_header(relpath, first, last, #all))
      table.insert(blocks, pandoc.CodeBlock(
        table.concat(all, "\n", first, last), pandoc.Attr("", { "fortl" })))
    end

    if eval then
      if attrs.show then
        local tmp = os.tmpname() .. ".frtl"
        write_file(tmp, src .. "\nit = " .. attrs.show .. "\n")
        result = run_fortl(tmp, 0, relpath)
        os.remove(tmp)
        shown_name = attrs.show
      else
        result = run_fortl(path, 0, relpath)
      end
    end
  else
    if echo then
      table.insert(blocks, pandoc.CodeBlock(text, pandoc.Attr("", { "fortl" })))
    end

    if eval then
      local session = attrs.session or "main"
      sessions[session] = sessions[session] or {}
      local prefix = table.concat(sessions[session], "\n")
      local offset = prefix == "" and 0 or count_lines(prefix)

      shown_name = attrs.show or last_binding(text)
      local program = (prefix == "" and "" or (prefix .. "\n")) .. text
      if shown_name and shown_name ~= "it" then
        program = program .. "\nit = " .. shown_name
      end
      program = program .. "\n"

      local tmp = os.tmpname() .. ".frtl"
      write_file(tmp, program)
      result = run_fortl(tmp, offset, "cell")
      os.remove(tmp)

      -- Only keep cells that work, so one broken cell doesn't break the rest
      if result.ok then
        table.insert(sessions[session], text)
      end
    end
  end

  if result then
    if not result.ok and not expect_error then
      quarto.log.warning("fortl cell failed:\n" .. result.message)
    elseif result.ok and expect_error then
      quarto.log.warning("fortl cell was expected to fail but succeeded")
    end
    if show_output then
      table.insert(blocks, output_block(shown_name, result, expect_error))
    end
  end

  return pandoc.Div(blocks, pandoc.Attr("", { "fortl-cell" }))
end

local function meta(m)
  local f = m.fortl
  if f then
    config.command = meta_string(f.command) or config.command
    config.repo_root = meta_string(f["repo-root"])
    config.repo_url = meta_string(f["repo-url"])
    if f["simplify-types"] ~= nil then
      config.simplify_types = f["simplify-types"] == true or
        meta_string(f["simplify-types"]) == "true"
    end
  end

  if quarto.doc.is_format("html") then
    quarto.doc.add_html_dependency({
      name = "fortl",
      version = "0.1.0",
      stylesheets = { "fortl.css" },
    })
  end
end

return {
  { Meta = meta },
  { CodeBlock = code_block },
}
