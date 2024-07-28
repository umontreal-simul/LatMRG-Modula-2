MODULE seekl;
(*# data ( stack_size => 5000H, heap_size  => 100) *)

FROM MYINOUT IMPORT WriteString, WriteLn;
FROM LATIO IMPORT SeekGen;

BEGIN
(*  WriteString (" Program  seekl  running ....");   WriteLn;  *)
SeekGen
END seekl.
