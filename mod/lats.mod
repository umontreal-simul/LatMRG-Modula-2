MODULE lats;
(*# data ( stack_size => 5000H, heap_size  => 100) *)

FROM MYINOUT IMPORT WriteString, WriteLn;
FROM LATIO IMPORT LatGen;

BEGIN
(*  WriteString (" Program  lats  running ....");   WriteLn;   *)
LatGen
END lats.
