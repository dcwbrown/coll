MODULE Codegen;  IMPORT w, Codespace, SYSTEM;


(* Register numbers:

   Reg  b    w    dw   qw        REX & Mod/RM encoding
   0    al   ax   eax  rax
   1    cl   cx   ecx  rcx
   2    dl   dx   edx  rdx
   3    bl   bx   ebx  rbx
   4    spl  sp   esp  rsp
   5    bpl  bp   ebp  rbp
   6    sil  si   esi  rsi
   7    dil  di   edi  rdi
   8    r8l  r8w  r8d  r8
   9    r9l  r9w  r9d  r9
   10   r10l r10w r10d r10
   10   r11l r11w r11d r11
   10   r12l r12w r12d r12
   10   r13l r13w r13d r13
   10   r14l r14w r14d r14
   10   r15l r15w r15d r15
   16   ah
   17   ch
   18   dh
   19   bh

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

CONST
     (* Dyadic operations *)
     AddOp*  = 0;  OrOp*   = 1;  AdcOp*  = 2;  SbbOp*  = 3;
     AndOp*  = 4;  SubOp*  = 5;  XorOp*  = 6;  CmpOp*  = 7;

     (* Dyadic direction *)
     From*   = 0;  To*     = 1;

     (* Dyadic operand kind *)
     Register* = 0;      AtAddress* = 1;  AtCodeOffset* = 2;
     AtScaledIndex* = 3; AtBasePlusIndex* = 4;

     (* Dyadic index scale factors *)
     Scale0* = 0;  Scale1* = 1;  Scale2* = 2;  Scale4* = 3;  Scale8* = 4;



TYPE
  i8  = SYSTEM.INT8;
  i16 = SYSTEM.INT16;
  i32 = SYSTEM.INT32;
  i64 = SYSTEM.INT64;

PROCEDURE Add8(byte: i16);
BEGIN Codespace.AddByte(SYSTEM.VAL(SYSTEM.BYTE, byte)) END Add8;

PROCEDURE Add16(word: i16);
BEGIN Add8(word MOD 100H); Add8(word DIV 100H) END Add16;

PROCEDURE Add32(dword: i32);
BEGIN Add16(SHORT(dword MOD 10000H)); Add16(SHORT(dword DIV 10000H)) END Add32;

PROCEDURE Add64(qword: i64);
BEGIN Add32(SHORT(qword MOD 100000000H)); Add32(SHORT(qword DIV 100000000H)) END Add64;

PROCEDURE AddConst(width: i16; const: i64);
BEGIN
  CASE width OF
  | 0: Codespace.AddByte(SYSTEM.VAL(SYSTEM.BYTE, const))
  | 1: Add16(SHORT(SHORT(const)))
  | 2: Add32(SHORT(const))
  ELSE Add64(const)
  END;
END AddConst;



PROCEDURE Dyadic*(inst, size, reg, direction, kind, rbase, rindex, scale: i16; offset: i32);
(*
   inst:
     0: Add  1: Or   2: Adc  3: Sbb
     4: And  5: Sub  6: Xor  7: Cmp
   size:
     0: byte  1: word  2: dword  3: qword
   direction:
     0 - reg from (kind,rbase,rindex,scale,offset)
     1 - (kind,rbase,rindex,scale,offset) from reg
   kind:
     0: rbase
     1: [offset]
     2: [RIP + offset]
     3: [rindex*scale + offset]
     4: [rbase + rindex*scale + offset]
   scale:
     0: rindex unsed
     1: rindex as is
     2: rindex * 2
     3: rindex * 4
     4: rindex * 8

   Instruction 0-7 encoding - instruction*8 plus:
     (0/2/4 are byte, 1/3/5 are word/dword/qword)
     0/1 - reg := reg op r/m
     2/3 - r/m := r/m op reg
     4/5 - alx := alx op immediate (al or eax)
*)
VAR
  rex, mode:  i16;
BEGIN
  w.Assert((reg < 16) & (rbase < 16) & (rindex < 16),
           "Dyadic does not yet support registers ah/bh/ch/dh.");

  w.Assert((scale = 0) OR (rindex = 0),"Dyadic - when passing scale=0 please also pass rindex=0.");

  w.Assert(rindex # 4, "RSP cannot be used as an index register.");

  (* 16 bit operand size override prefix *)
  IF size = 1 THEN Add8(66H) END;

  (* REX prefix *)
  rex := 0;
  IF rbase  >= 8 THEN  INC(rex,1);  rbase  := rbase  MOD 8 END;
  IF rindex >= 8 THEN  INC(rex,2);  rindex := rindex MOD 8 END;
  IF reg    >= 8 THEN  INC(rex,4);  reg    := reg    MOD 8 END;
  IF size   >  2 THEN  INC(rex,8)                          END;
  IF rex # 0 THEN Add8(40H + rex) END;

  (* Instruction opcode *)
  inst := inst * 8;
  IF size # 0      THEN INC(inst)   END;  (* Instruction size > byte *)
  IF direction = 0 THEN INC(inst,2) END;  (* Reg from various types  *)
  Add8(inst);

  IF kind = 0 THEN                        (* Register to register operation *)
    Add8(0C0H + reg*8 + rbase)            (* ModRM: 2/11, 3/reg, 3/rbase *)

  ELSIF kind = 1 THEN                     (* [offset] *)
    Add8(reg*8 + 4);                      (* ModRM: 2/00, 3/reg, 3/100 - Use SIB addressing *)
    Add8(25H);                            (* SIB:   2/00, 3/100, 3/101 - [disp32] addressing *)
    Add32(offset)

  ELSIF kind = 2 THEN                     (* [RIP + offset] *)
    Add8(reg*8 + 5);                      (* ModRM: 2/00, 3/reg, 3/101 *)
    Add32(offset)

  ELSIF kind = 3 THEN                     (* [rindex*scale + offset] *)
    Add8(reg*8 + 4);                      (* ModRM: 2/00, 3/reg, 3/100 - Use SIB addressing *)
    Add8((scale-1)*64 + rindex*8 + 5);    (* SIB: 2/scale, 3/rindex, 3/101 *)
    Add32(offset)

  ELSE                                    (* General case *)
    mode := 0;
    IF (offset # 0) OR (rbase = 5) THEN
      IF (offset < 128) & (offset >= -128) THEN mode := 1 ELSE mode := 2 END
    END;

    IF (scale = 0) & (rbase # 4) THEN     (* No SIB needed *)
      Add8(mode*64 + reg*8 + rbase)        (* ModRM: 2/mode, 3/reg, 3/rbase *)

    ELSE                                  (* Using SIB *)
      Add8(mode*64+ reg*8 + 4);           (* ModRM: 2/mode, 3/reg, 3/100 - [SIB] *)

      IF scale = 0 THEN
        Add8((scale-1)*64 + 32 + rbase);  (* SIB: 2/scale, 3/100,  3/rbase *)
      ELSE
        Add8((scale-1)*64 + rindex*8 + rbase);  (* SIB: 2/scale, 3/rindex, 3/rbase *)
      END
    END;

    IF mode = 1 THEN Add8(SHORT(SHORT(offset))) ELSIF mode = 2 THEN Add32(offset) END
  END
END Dyadic;


PROCEDURE Ret*;  BEGIN Add8(0C3H) END Ret;


(*PROCEDURE AddInt*(r1, r2, width: i16);
BEGIN
  Dyadic(AddOp, width, r1, From, Register, r2, Scale0, 0, 0)
END AddInt;
*)

PROCEDURE ExchangeReg*(r1, r2, width: i16);
VAR prefix, rex, modrm, extra, instruction: i16;
BEGIN
  w.Assert(r1 = 0,  "ExchangeReg currenty only supporting al/ax/eax/rax as r1.");
  w.Assert(r2 < 16, "ExchangeReg currenty not supporting r2 as ah,bh, ch,dh.");
  prefix := 0;  rex := 0;  modrm := 0;  extra := 0; instruction := 90H;
  CASE width OF
  | 0: extra := 86H;  instruction := 0C0H;
       IF r2 > 3 THEN IF r2 < 8 THEN rex := 40H ELSE rex := 41H END END
  | 1: prefix := 66H;
       IF r2 > 7 THEN rex := 41H END;
  | 2: IF r2 = 0 THEN prefix := 87H; instruction := 0C0H END;
       IF r2 > 7 THEN rex := 41H END;
  ELSE IF r2 < 8 THEN rex := 48H ELSE rex := 49H END;
  END;
  IF prefix # 0 THEN Add8(prefix) END;
  IF rex    # 0 THEN Add8(rex)    END;
  IF modrm  # 0 THEN Add8(modrm)  END;
  IF extra  # 0 THEN Add8(extra)  END;
  Add8(instruction + (r2 MOD 8));
END ExchangeReg;

PROCEDURE CopyReg*(target, source, width: i16);
BEGIN
  w.Assert(target = 0,  "CopyReg currenty only supporting reg 0 as target.");
  w.Assert(source < 16, "CopyReg currenty not supporting source ah,bh, ch,dh.");
  CASE width OF
  | 0: IF source > 3 THEN IF source < 8 THEN Add8(40H) ELSE Add8(44H) END END
  | 1: Add8(66H);  IF source > 7 THEN Add8(44H) END
  | 2: IF source > 7 THEN Add8(44H) END
  ELSE IF source < 8 THEN Add8(48H) ELSE Add8(4CH) END
  END;
  IF width = 0 THEN Add8(88H) ELSE Add8(89H) END;
  Add8(0C0H + (source MOD 8) * 8);
END CopyReg;

PROCEDURE LoadConst*(reg, width: i16; const: i64);
BEGIN
  (* Special case handling for small constants into dword and qword registers *)
  IF (width >= 2) & (const >= 0) & (const < 128) THEN
    IF const = 0 THEN
      Dyadic(XorOp, 2, reg, From, Register, reg, Scale0, 0, 0)
    ELSE
      Add8(6AH);  (* Push immediate 8 bit *)
      Add8(SHORT(SHORT(SHORT(const))));
      IF reg >= 8 THEN Add8(44H) END;  (* REX.R *)
      Add8(58H + reg MOD 8)
    END
  ELSE
    IF (width = 3) & (const >= 0) & (const < 100000000H) THEN width := 2 END;
    IF reg < 8 THEN
      CASE width OF
      | 0: IF reg > 3 THEN Add8(40H) END;  Add8(0B0H+reg);
      | 1: Add8(66H);                      Add8(0B8H+reg);
      | 2:                                 Add8(0B8H+reg);
      ELSE Add8(48H);                      Add8(0B8H+reg);
      END
    ELSIF reg < 16 THEN
      CASE width OF
      | 0:             Add8(41H);  Add8(0B0H + reg-8);
      | 1: Add8(66H);  Add8(41H);  Add8(0B8H + reg-8);
      | 2:             Add8(41H);  Add8(0B8H + reg-8);
      ELSE             Add8(49H);  Add8(0B8H + reg-8);
      END
    ELSE
      w.Assert(width = 0, "LoadConst reg > 15 (ah, bh, ch or dh) but width # 0.");
      w.Assert(reg < 20,  "LoadConst reg > 19: no such register.");
      Add8(0B4H + reg-16);
    END;
    AddConst(width, const)
  END;
END LoadConst;



PROCEDURE TestCodeGeneration*;
VAR entry: Codespace.Entry;  rax: i64;
BEGIN
  Codespace.Allocate(4096);

  entry := Codespace.GetEntry();
  LoadConst(0, 3, 11H);
  Ret;

  Codespace.Align(16);  AddConst(0, 11H);
  Codespace.Align(16);  AddConst(1, 1122H);
  Codespace.Align(16);  AddConst(2, 11223344H);
  Codespace.Align(16);  AddConst(3, 1122334455667788H);

  Codespace.Dump(0,60H);

  w.sl("Calling code.");
  rax := entry();
  w.s("Called code completed, rax = "); w.x(rax, 16); w.nb; w.sl("H.");

END TestCodeGeneration;


PROCEDURE TestLoadConst*(reg: i16; const: i64);
VAR entry: Codespace.Entry;  rax: i64;
BEGIN
  w.s("TestLoadConst: register "); w.i(reg); w.nb; w.s(", const "); w.x(const, 16); w.nb; w.sl("H.");
  Codespace.Origin(0);  Codespace.Bss(16);  Codespace.Origin(0);
  entry := Codespace.GetEntry();
  LoadConst(reg, 3, const);
  IF reg # 0 THEN CopyReg(0, reg, 3) END;
  Ret;
  Codespace.Dump(0,10H);
  rax := entry();
  w.Assert(rax = const, "TestLoadConst failed.");
END TestLoadConst;


PROCEDURE TestLoadConstWithExchange*(reg: i16; const: i64);
VAR entry: Codespace.Entry;  rax: i64;
BEGIN
  w.s("TestLoadConstWithExchange: register "); w.i(reg); w.nb; w.s(", const "); w.x(const, 16); w.nb; w.sl("H.");
  Codespace.Origin(0);  Codespace.Bss(32);  Codespace.Origin(0);
  entry := Codespace.GetEntry();
  IF reg # 0 THEN ExchangeReg(0, reg, 3) END;
  LoadConst(reg, 3, const);
  IF reg # 0 THEN ExchangeReg(0, reg, 3) END;
  Ret;
  Codespace.Dump(0,20H);
  rax := entry();
  w.Assert(rax = const, "TestLoadConstWithExchange failed.");
END TestLoadConstWithExchange;


PROCEDURE TestLoadRegs*(const: i64); (* Test loading all except SP, BP *)
VAR reg: i16;
BEGIN
  (*
  FOR reg := 0 TO  3 DO TestLoadConst(reg, const) END;
  FOR reg := 6 TO 15 DO TestLoadConst(reg, const) END;
  *)
  FOR reg := 0 TO 15  DO TestLoadConstWithExchange(reg, const) END;
END TestLoadRegs;




END Codegen.

