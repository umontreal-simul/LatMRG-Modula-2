MODULE latsr;
(*# data ( stack_size => 5000H, heap_size  => 100) *)

FROM LATIO   IMPORT LatGen;
FROM MYINOUT IMPORT WriteString, WriteLn;

BEGIN
WriteString (" Program  lats  running ....");  WriteLn;
LatGen
END latsr.
