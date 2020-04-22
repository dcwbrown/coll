MODULE test;  IMPORT w, Codespace, Codegen, (* Functions *) Jobs, Prefix, SYSTEM;


(* Register numbers:

   Reg   b    w    dw   qw        REX & Mod/RM encoding
   0     al   ax   eax  rax
   1     cl   cx   ecx  rcx
   2     dl   dx   edx  rdx
   3     bl   bx   ebx  rbx
   4     spl  sp   esp  rsp
   5     bpl  bp   ebp  rbp
   6     sil  si   esi  rsi
   7     dil  di   edi  rdi
   8     r8l  r8w  r8d  r8
   9     r9l  r9w  r9d  r9
   10    r10l r10w r10d r10
   10    r11l r11w r11d r11
   10    r12l r12w r12d r12
   10    r13l r13w r13d r13
   10    r14l r14w r14d r14
   10    r15l r15w r15d r15
   16    ah
   17    ch
   18    dh
   19    bh

   Widths:
   0    byte  -  8 bits
   1    word  - 16 bits
   2    dword - 32 bits
   3    qword - 64 bits

   REX  0010WRXB
   W    0: 32 bit operand size,  1: 64 bit register size
   R    provides top bit of ModRM register field
   X    provides top bit of SIB index register field
   B    provides top bit of ModRM rm field, SIB base field or opcode reg field

   MODRM 2/mod,3/reg,3/rm
   mod 0-2  register to/from SIB or memory
         3  register to/from register

*)

TYPE
  i8  = SYSTEM.INT8;
  i16 = SYSTEM.INT16;
  i32 = SYSTEM.INT32;
  i64 = SYSTEM.INT64;




BEGIN
  (*
  w.sl("Code generator test harness.");
  Codegen.TestCodeGeneration;
  IF FALSE THEN
    Codegen.TestLoadRegs(0);
    Codegen.TestLoadRegs(1);
    Codegen.TestLoadRegs(-1);
    Codegen.TestLoadRegs(0FFFFFFFFH);
    Codegen.TestLoadRegs(100000000H)
  END;
  *)
  (* Functions.Test; *)
  Jobs.Test
END test.

