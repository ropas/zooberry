(*
 * Copyright (c) 2017-present,
 * Programming Research Laboratory (ROPAS), Seoul National University, Korea
 * This software is distributed under the term of the BSD-3 clause license.
 *)
open StringFun
(*
  [return type]
  clean_ret
  taint_ret
  dst_ret
  src_ret
  src_ret_alloc
*)

let read =
(* <cstring> ( <string.h> ) *)
(* Copying *)
M.empty
|> M.add "memcpy" {args = [dst; src; skip]; ret = dst_ret}
|> M.add "memmove" {args = [dst; src; skip]; ret = dst_ret}
|> M.add "strcpy" {args = [dst; src]; ret = dst_ret}
|> M.add "strncpy" {args = [dst; src; skip]; ret = dst_ret}
(* Concatenation *)
|> M.add "strcat" {args = [dst; src]; ret = dst_ret}
|> M.add "strncat" {args = [dst; src; skip]; ret = dst_ret}
(* Comparison *)
|> M.add "memcmp" {args = [src; src; skip]; ret = src_ret}
|> M.add "strcmp" {args = [src; src]; ret = src_ret}
|> M.add "strcoll" {args = [src; src]; ret = src_ret}
|> M.add "strncmp" {args = [src; src; skip]; ret = src_ret}
|> M.add "strxfrm" {args = [dst; src; skip]; ret = dst_ret}
(* Searching *)
|> M.add "memchr" {args = [src; skip; skip]; ret = src_ret}
|> M.add "strchr" {args = [src; skip]; ret = src_ret}
|> M.add "strcspn" {args = [src; skip; skip]; ret = src_ret}
|> M.add "strpbrk" {args = [src; skip]; ret = src_ret}
|> M.add "strrchr" {args = [src; skip]; ret = src_ret}
|> M.add "strspn" {args = [src; skip]; ret = src_ret}
|> M.add "strstr" {args = [src; skip]; ret = src_ret}
|> M.add "strtok" {args = [src; skip]; ret = src_ret}
(* Other *)
|> M.add "memset" {args = [dst; src; skip]; ret = dst_ret}
|> M.add "strerror" {args = [skip]; ret = clean_ret}
|> M.add "strlen" {args = [src]; ret = src_ret}
(* <cctype> ( <ctype.h> ) *)
(* Character conversion functions *)
|> M.add "tolower" {args = [src]; ret = src_ret}
|> M.add "toupper" {args = [src]; ret = src_ret}
(* <cmath> ( <math.h> ) *)
|> M.add "log" {args = [src]; ret = src_ret}
|> M.add "sin" {args = [src]; ret = src_ret}
|> M.add "tan" {args = [src]; ret = src_ret}
|> M.add "cos" {args = [src]; ret = src_ret}
|> M.add "acos" {args = [src]; ret = src_ret}
|> M.add "asin" {args = [src]; ret = src_ret}
|> M.add "atan" {args = [src]; ret = src_ret}
|> M.add "atan2" {args = [src]; ret = src_ret}
|> M.add "pow" {args = [src; src]; ret = src_ret}
|> M.add "sqrt" {args = [src]; ret = src_ret}
|> M.add "abs" {args = [src]; ret = src_ret}
|> M.add "fabs" {args = [src]; ret = src_ret}
(* <cstdio> ( <stdio.h> ) *)
|> M.add "sscanf" {args = [src; skip; dst_va]; ret = taint_ret}

(* GNU FUNCTION *)
|> M.add "_IO_getc" {args = [skip]; ret = taint_ret}
|> M.add "__errno_location" {args = []; ret = clean_ret}
|> M.add "socket" {args = [skip; skip; skip]; ret = clean_ret}
|> M.add "access" {args = [skip; skip]; ret = clean_ret}
|> M.add "chown" {args = [skip; skip; skip]; ret = clean_ret}
|> M.add "uname" {args = [skip]; ret = clean_ret}
|> M.add "mkdir" {args = [skip; skip]; ret = clean_ret}
|> M.add "mkfifo" {args = [skip; skip]; ret = clean_ret}
|> M.add "setgroups" {args = [skip; skip]; ret = clean_ret}
|> M.add "seteuid" {args = [skip]; ret = clean_ret}
|> M.add "setegid" {args = [skip]; ret = clean_ret}
|> M.add "htonl" {args = [src]; ret = src_ret}
|> M.add "htons" {args = [src]; ret = src_ret}
|> M.add "ntohl" {args = [src]; ret = src_ret}
|> M.add "ntohs" {args = [src]; ret = src_ret}
|> M.add "pipe" {args = [skip]; ret = clean_ret}
|> M.add "time" {args = [skip]; ret = clean_ret}
|> M.add "ctime" {args = [skip]; ret = clean_ret}
|> M.add "drand48" {args = []; ret = clean_ret}
|> M.add "rand" {args = []; ret = clean_ret}
|> M.add "getenv" {args = [skip]; ret = taint_ret}
|> M.add "cuserid" {args = []; ret = clean_ret}
|> M.add "getlogin" {args = []; ret = clean_ret}
|> M.add "getlogin_r" {args = [skip; skip]; ret = clean_ret}
|> M.add "getpid" {args = []; ret = clean_ret}
|> M.add "stat" {args = [skip; skip]; ret = clean_ret}
|> M.add "fstat" {args = [skip; skip]; ret = clean_ret}
|> M.add "lstat" {args = [skip; skip]; ret = clean_ret}
|> M.add "strdup" {args = [src]; ret = src_ret_alloc}
|> M.add "waitpid" {args = [skip; skip; skip]; ret = clean_ret}
|> M.add "getrlimit" {args = [skip; skip]; ret = clean_ret}
|> M.add "pthread_create" {args = [skip; skip; skip; skip]; ret = clean_ret}
|> M.add "pthread_getspecific" {args = [skip; skip]; ret = clean_ret}
|> M.add "re_match" {args = [skip; skip; skip; skip; skip]; ret = clean_ret}
|> M.add "re_search" {args = [skip; skip; skip; skip; skip]; ret = clean_ret}
|> M.add "setsockopt" {args = [skip; skip; skip; skip]; ret = clean_ret}
|> M.add "system" {args = [src]; ret = src_ret}
|> M.add "setlocale" {args = [skip; skip]; ret = clean_ret}

(* Linux File IO *)
|> M.add "write" {args = [skip; skip; skip]; ret = clean_ret}
|> M.add "read" {args = [skip; dst_ext; skip]; ret = taint_ret}
|> M.add "fread" {args = [dst_ext; skip; skip; skip]; ret = taint_ret}
|> M.add "_IO_getc" {args = [skip]; ret = taint_ret}
|> M.add "getchar" {args = []; ret = taint_ret}
|> M.add "recv" {args = [skip; dst_ext; skip; skip]; ret = taint_ret}
|> M.add "nl_langinfo" {args = [skip]; ret = clean_ret}
|> M.add "readlink" {args = [skip; dst_ext; skip]; ret = taint_ret}
|> M.add "open" {args = [skip; skip; skip]; ret = clean_ret}
|> M.add "close" {args = [skip]; ret = clean_ret}
|> M.add "unlink" {args = [skip]; ret = clean_ret}
|> M.add "mmap" {args = [src; skip; skip]; ret = src_ret_alloc}
(* NOTE : It is not precise *)
|> M.add "select" {args = [skip; skip; skip; skip; skip]; ret = clean_ret}

(* etc *)
|> M.add "scanf" {args = [skip; dst_va_ext]; ret = clean_ret}
|> M.add "atoi" {args = [src]; ret = src_ret}
|> M.add "strtod" {args = [src; skip]; ret = src_ret}
|> M.add "strtol" {args = [src; skip; skip]; ret = src_ret}
|> M.add "strtoul" {args = [src; skip; skip]; ret = src_ret}
|> M.add "realloc" {args = [src; skip]; ret = src_ret_alloc}
|> M.add "gettext" {args = [src]; ret = src_ret}
|> M.add "dgettext" {args = [src]; ret = src_ret}
|> M.add "dcgettext" {args = [src]; ret = src_ret}
