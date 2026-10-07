# json2dir: create the directory tree a JSON document describes, in the current directory.
# Implements RFC J2D-1 (https://github.com/kitsunoff/awesome-json2dir/blob/main/spec/rfc-json2dir.md).
# CBQN only: •file for (lstat-based) type queries and unlink, •FFI to libc for
# open/write/fchmod/mkdir/symlink. Bytes are kept as number lists (0-255) throughout.

libc ← ↑‿"libc.so.6"
open    ← libc •FFI "i32"‿"open"‿"*u8"‿"i32"‿"u32"
write   ← libc •FFI "i64"‿"write"‿"i32"‿"*u8"‿"u64"
close   ← libc •FFI "i32"‿"close"‿"i32"
fchmod  ← libc •FFI "i32"‿"fchmod"‿"i32"‿"u32"
mkdir   ← libc •FFI "i32"‿"mkdir"‿"*u8"‿"u32"
symlink ← libc •FFI "i32"‿"symlink"‿"*u8"‿"*u8"
umask   ← libc •FFI "u32"‿"umask"‿"u32"

Bytes ← -⟜@∘•ToUTF8                  # string -> UTF-8 byte numbers
Str   ← •FromUTF8 @⊸+                # UTF-8 byte numbers -> string
Err   ← {Write 2‿𝕩‿(≠𝕩)}∘Bytes       # write a string to stderr

# ---- §3: strict UTF-8, checked on the whole byte vector at once ----
Utf8OK ← {
  cont ← (𝕩≥128)∧𝕩<192
  len  ← (128‿194‿224‿240‿245⍋𝕩) ⊏ 1‿0‿2‿3‿4‿0   # sequence length announced by each byte as a lead
  st   ← /¬cont                                  # positions of lead bytes
  l    ← st⊏len
  lead ← st⊏𝕩
  sec  ← (st+1)⊏𝕩∾0                              # second byte of each sequence
  bad  ← ((lead=224)∧sec<160) ∨ ((lead=237)∧sec>159) ∨ ((lead=240)∧sec<144) ∨ (lead=244)∧sec>143
  (∧´l>0) ∧ (¬∨´bad) ∧ (st∾≠𝕩) ≡ 0∾st+l           # every sequence complete, no overlong/surrogate/too big
}

# 1 where the byte is preceded by an odd run of backslashes
Escaped ← { bs←𝕩=92 ⋄ c←+`bs ⋄ »2|c-⌈`c×¬bs }

# code point -> UTF-8 bytes
Enc ← {
  𝕩<128 ? ⋈𝕩 ;
  n ← 2++´𝕩≥2048‿65536
  v ← ⌊𝕩÷64⋆⌽↕n
  ((⊑v)∾64|1↓v) + ((n-2)⊑192‿224‿240)∾(n-1)⥊128
}

# decode the escapes of one string body (bytes between the quotes)
Unesc ← {
  ¬∨´𝕩=92 ? 𝕩 ;
  es ← (𝕩=92)∧¬Escaped 𝕩                        # escape-introducing backslashes
  st ← /es ⋄ k ← (st+1)⊏𝕩
  "invalid escape in string" ! ∧´k∊"""\/bfnrtu"-@
  u  ← k=@-˜'u'
  hv ← ("0123456789abcdefABCDEF"-@) ⊐ (𝕩∾6⥊0) ⊏˜ st +⌜ 2+↕4
  "invalid \u escape in string" ! ∧´(¬u) ∨ ∧´˘hv<22
  cu ← +´˘ (hv-6×hv≥16) ×⎉1 4096‿256‿16‿1
  cp ← (u×cu) + (¬u) × (("""\/bfnrt"-@)⊐k) ⊏ 34‿92‿47‿8‿12‿10‿13‿9‿0
  # §3.5: surrogates must come in adjacent high/low \u pairs
  hi ← u∧(cp≥55296)∧cp<56320
  lo ← u∧(cp≥56320)∧cp<57344
  ph ← hi ∧ («lo) ∧ (st+6) = «st
  "string contains an unpaired surrogate" ! ¬∨´(hi∧¬ph) ∨ lo∧¬»ph
  cp ↩ (ph × 65536 + (1024×cp-55296) + 56320-˜«cp) + cp × ¬ph
  out ← (»ph) {𝕨 ? ⟨⟩ ; Enc 𝕩}¨ cp               # the low half of a pair emits nothing
  cov ← 1¨⌾((∾st+⟜↕¨2+4×u)⊸⊏) 0¨𝕩               # bytes covered by escapes
  ∾ (es∨¬cov) / out⌾(st⊸⊏) ⋈¨𝕩
}

objOK ← "{}"‿"{K"‿"K:"‿":"""‿":V"‿""","‿"""}"‿"V,"‿"V}"‿",K"
arrOK ← "[]"‿"["""‿"[V"‿""","‿"""]"‿"V,"‿"V]"‿","""‿",V"

# Parse and validate the whole document. Result: n⊸⊑ gives the members of the object opened
# at token n, as name‿value pairs; a value is 0‿bytes (file), 1‿bytes (script),
# 2‿target (link) or 3‿token (directory). The root object is token 0.
Parse ← {𝕊 b:
  q   ← (b=34)∧¬Escaped b                       # unescaped quotes
  ins ← ≠`q                                     # 1 from an opening quote up to its closing quote
  "unterminated string" ! ¬¯1⊑0∾ins
  "control character in string" ! ¬∨´(ins∧¬q)∧b<32
  out ← ¬ins∨q
  sc  ← b∊"{}[]:,"-@
  "invalid JSON (numbers, true, false and null are not allowed)" ! ∧´(¬out)∨sc∨b∊9‿10‿13‿32
  tk   ← @+b⊏˜/(out∧sc)∨ins∧q                    # tokens; a string is its opening quote
  ss   ← (/ins∧q) {Unesc (𝕨+1)↓𝕩↑b}¨ /q∧¬ins     # decoded strings, in order
  si  ← ¯1++`tk='"'                              # string index of each token

  # structure: depth, a single root object
  n ← ≠tk ⋄ o ← tk∊"{[" ⋄ c ← tk∊"}]" ⋄ dp ← +`o-c
  "invalid JSON" ! (n>0) ∧ (0=¯1⊑0∾dp) ∧ ∧´0<¯1↓dp
  "the root of the document must be an object" ! '{'=⊑tk

  # Group the tokens by the container directly holding them; each opener also appears in
  # its parent's group as a value V. Sorting by (level, position) lays every container out
  # contiguously as  opener  member tokens  closer.
  oi ← /o
  et ← tk∾'V'¨oi ⋄ ek ← (dp+c)∾oi⊏dp-1 ⋄ ep ← (↕n)∾oi
  k  ← ek>0
  g  ← ⍋(k/ek)≍˘k/ep
  sv ← g⊏k/et ⋄ sk ← g⊏k/ek ⋄ sp ← g⊏k/ep
  ow ← (⌈`(sv∊"{[")×1+↕≠sv)-1                    # sorted position of each token's opener
  ct ← ow⊏sv                                    # its container type
  rl  ← sv + ('K'-'"') × (ct='{')∧(sv='"')∧(»sv)∊"{,"   # strings in key position become K
  chk ← (sk=»sk) ∧ ¬(»rl)∊"}]"
  ok  ← ((ct='{')∧((»rl)≍¨rl)∊objOK) ∨ (ct='[')∧((»rl)≍¨rl)∊arrOK
  "invalid JSON" ! ∧´ok∨¬chk
  "mismatched brackets" ! ∧´(¬sv∊"}]") ∨ (sv='}')=ct='{'

  # §4.4: arrays are exactly ["link", target] or ["script", content]
  ai ← /tk='['
  "an array must be [""link"", target] or [""script"", content]" ! ∧´{""",""]"≡4↑(𝕩+1)↓tk}¨ai
  kinds ← ss⊏˜si⊏˜ai+1 ⋄ pays ← ss⊏˜si⊏˜ai+3
  ki ← ("script"‿"link" Bytes¨⊸⊐ kinds)
  "unknown array kind" ! ∧´ki<2
  "a link target cannot contain NUL" ! ¬∨´(ki=1)∧(∨´0=⊢)¨pays

  # §4.2.1: names
  kp ← /rl='K'
  names ← ss⊏˜si⊏˜kp⊏sp
  Bad ← {(0=≠𝕩) ∨ (𝕩≡⋈46) ∨ (𝕩≡46‿46) ∨ ∨´𝕩∊0‿47}
  "invalid name" ! ¬∨´Bad¨names

  # members: key at sorted position p, its value at p+2
  vt ← sv⊏˜kp+2 ⋄ vp ← sp⊏˜kp+2
  Val ← {𝕊 t‿p:
    {𝕩 ? 0‿(ss⊑˜si⊑˜p) ;
     '{'=p⊑tk ? 3‿p ;
     ⟨1+(Bytes "link")≡ss⊑˜si⊑˜p+1, ss⊑˜si⊑˜p+3⟩} t='"'
  }
  ((sp⊏˜ow⊏˜kp)∾n) ⊔ names ⋈¨ Val¨ vt⋈¨vp
}

# mode bits as 9 booleans and back
Bits ← 2|⌊∘÷⟜(2⋆↕9)
Num  ← +´(2⋆↕9)⊸×

WriteFile ← {𝕊 mode‿exec‿p‿content:
  fd ← Open ⟨p∾0, 1+64+128+131072, 438⟩         # O_WRONLY|O_CREAT|O_EXCL|O_NOFOLLOW, 0666
  ("cannot create file "∾Str p) ! fd≥0
  {0=≠𝕩 ? @ ; r ← Write fd‿𝕩‿(≠𝕩) ⋄ ("cannot write "∾Str p) ! r>0 ⋄ 𝕊 r↓𝕩} content
  {𝕩 ? ("cannot chmod "∾Str p) ! 0=Fchmod fd‿mode ; @} exec
  Close ⟨fd⟩
}

Walk ← {tree‿mode‿dir 𝕊 obj:
  m ← obj⊑tree
  m ↩ (⌽∊⌽⊑¨m)/m                                # duplicate names: the last one wins
  {𝕊 name‿(kind‿v):
    p ← dir∾47∾name ⋄ s ← Str p
    t ← {•file.Exists 𝕩 ? •file.Type 𝕩 ; ' '} s  # lstat: a symlink is reported as 'l'
    Rm ← {𝕩 ? •file.Remove s ; @}
    {𝕩 ?                                         # object: reuse a directory, replace anything else
      {𝕩 ? Rm t≠' ' ⋄ ("cannot create directory "∾s) ! 0=Mkdir ⟨p∾0, 511⟩ ; @} t≠'d'
      tree‿mode‿p Walk v ;
      (s∾": a directory is in the way") ! t≠'d'
      Rm t≠' '
      {𝕩 ? ("cannot create link "∾s) ! 0=Symlink ⟨v∾0, p∾0⟩ ; WriteFile mode‿(kind=1)‿p‿v} kind=2
    } kind=3
  }¨ m
}

Main ← {𝕊:
  b ← -⟜@ •file.Bytes "/dev/stdin"
  b ↓˜↩ 3×239‿187‿191≡3↑b                       # §3: a leading BOM may be ignored
  "input is not valid UTF-8" ! Utf8OK b
  tree ← Parse b
  um ← Umask ⟨0⟩ ⋄ Umask ⟨um⟩
  mode ← Num (Bits 73) ∨ (Bits 438) ∧ ¬Bits um   # (0666 & ~umask) | 0111 for scripts
  dir ← Bytes •wdpath
  dir ↓˜↩ -47=¯1⊑dir
  tree‿mode‿dir Walk 0
  0
}

{
  𝕩 ? Err "usage: json2dir < document.json"∾@+10 ⋄ •Exit 2 ;
  •Exit Main⎊{𝕊: Err "json2dir: "∾(•CurrentError@)∾@+10 ⋄ 1} @
} 0<≠•args
