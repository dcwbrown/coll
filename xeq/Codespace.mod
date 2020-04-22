MODULE Codespace;  IMPORT w, SYSTEM;


TYPE
  Address    = SYSTEM.ADDRESS;
  i64        = SYSTEM.INT64;
  i32        = SYSTEM.INT32;
  CodeMemory = POINTER [1] TO ARRAY 65536 OF SYSTEM.BYTE;
  Entry*     = PROCEDURE(): i64;


VAR
  CodeAddress: SYSTEM.ADDRESS;
  Memory:      CodeMemory;
  Offset:      INTEGER;
  Limit:       INTEGER;


PROCEDURE -Aincludemman '#include <sys/mman.h>';
PROCEDURE -osmemmap(size: SYSTEM.ADDRESS; protection: SYSTEM.INT32): SYSTEM.ADDRESS
  "(ADDRESS)mmap(0, size, protection, MAP_ANONYMOUS|MAP_PRIVATE, 0, 0)";


PROCEDURE Allocate*(size: INTEGER);
BEGIN
  CodeAddress := osmemmap(size, 7);  (* PROT_READ | PROT_WRITE | PROT_EXECUTE *)
  w.Assert(CodeAddress > 0, "Could not allocate code space.");
  w.s("Codespace allocated at "); w.x(CodeAddress,1); w.sl(".");
  Memory := SYSTEM.VAL(CodeMemory, CodeAddress);
  Offset := 0;
  Limit  := size;
END Allocate;

PROCEDURE Origin*(offset: INTEGER);  BEGIN Offset := offset END Origin;

PROCEDURE GetEntry*(): Entry;
BEGIN RETURN SYSTEM.VAL(Entry, CodeAddress + Offset) END GetEntry;

PROCEDURE GetOffset*(): i64;
BEGIN RETURN Offset END GetOffset;

PROCEDURE Align*(alignment: i32);  (* Parameter must be a power of 2 *)
VAR partial: i32;
BEGIN
  partial := Offset MOD alignment;
  Offset := Offset + alignment - partial;
END Align;

PROCEDURE AddByte*(b: SYSTEM.BYTE);
BEGIN
  w.Assert(Offset < Limit, "Codespace memory overflow.");
  (*w.s("AddByte "); w.x(SYSTEM.VAL(BYTE, b),1); w.s("hex at offset "); w.i(Offset); w.sl(".");*)
  Memory[Offset] := b;
  INC(Offset);
END AddByte;

PROCEDURE Bss*(length: INTEGER);
VAR i: INTEGER;
BEGIN FOR i := 1 TO length DO AddByte(0) END END Bss;

PROCEDURE whd(d: INTEGER);  (* Write hex digit. *)
BEGIN
  d := d MOD 16;
  IF d < 10 THEN w.c(CHR(ORD('0') + d))
  ELSE w.c(CHR(ORD('a') + d-10)) END
END whd;

PROCEDURE Dump*(offset, length: i64);
VAR start, limit: Address;  i, j: i64; byte: INTEGER;
BEGIN
  start := ((CodeAddress+offset) DIV 16) * 16;
  limit := ((start+length+15)    DIV 16) * 16;
  i := start;
  WHILE i < limit DO
    w.x(i,16); w.nb; w.s(":  ");
    FOR j := 0 TO 15 DO
      byte := SYSTEM.VAL(SYSTEM.INT8, Memory[i-CodeAddress + j]) MOD 256;
      whd(byte DIV 16);  whd(byte);  w.c(' ');
      IF j MOD 8 = 7 THEN w.c(' ') END;
    END;

    w.c(' ');

    FOR j := 0 TO 15 DO
      byte := SYSTEM.VAL(SYSTEM.INT8, Memory[i-CodeAddress + j]) MOD 256;
      IF (byte <= 32) OR (byte >= 127) THEN w.c('.') ELSE w.c(CHR(byte)) END;
    END;

    w.l;
    INC(i, 16);
  END;
END Dump;


BEGIN
END Codespace.