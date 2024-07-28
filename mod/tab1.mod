MODULE tab1;
(* This program assumes the representation SI SI  *)

FROM LATBASIS IMPORT Basis, WriteBasis;
FROM REDBAS   IMPORT InitREDBAS, Critere2Type;
FROM REDBAS2  IMPORT InitREDBAS2;
FROM MRG      IMPORT InitMRG, Test, TestType, VerifyType, OutputType, 
                     LatticeType, LatType, Q2, D2, S2, BuildBasis;
FROM MULT     IMPORT MDim, MScal, MVect, MCreateScal, MCreateVect;
FROM CONSTANT IMPORT BDim;
FROM CONVERT  IMPORT SupToMScal;
FROM SUPINT   IMPORT SuperInteger, Create;
FROM SUPCONV  IMPORT IntToSup;
FROM SUPARITH IMPORT Multiply, MultiplyIntSup;
FROM MYINOUT  IMPORT WriteString, WriteInt, WriteLn;
FROM NUM      IMPORT WriteLR, Sqrt;

VAR
   SaveD, SaveS : ARRAY [0..6] OF ARRAY [0..40] OF LONGREAL;
   aa, mm : SuperInteger;
   a      : MVect;
   m      : MScal;
   i, j, t1, t2 : BDim;


PROCEDURE TestIt (j : INTEGER);
   VAR
   i   : BDim;
   BEGIN
   WriteLn;
   WriteString ("*********************************************");  WriteLn;
   WriteString ("Starting test with j = ");  WriteInt (j, 2);  WriteLn;
   SupToMScal (mm, m);  SupToMScal (aa, a[1]);
   InitMRG (m, 1, t2);
   Test (a, Spectral, t1, t2, Verify2, CurOut); 
   FOR i := t1 TO t2 DO  SaveD [j, i] := Sqrt (D2 [i])  END;
   FOR i := t1 TO t2  DO  SaveS [j, i] := Sqrt (S2 [i])  END;
   END TestIt;

BEGIN
Create (mm, 2);   Create (aa, 2);
MCreateScal (m);  MCreateVect (a, 0, 9);
t1 := 2;  t2 := 5;
InitREDBAS (t2, Hermite);  InitREDBAS2 (t2);

LatType := Full;
IntToSup (2147483647, mm);
IntToSup (742938285, aa);
TestIt (1);
IntToSup (16807, aa);
TestIt (2);
(*
IntToSup (630360016, aa);
TestIt (3);

LatType := PrimePower;
IntToSup (536870912, mm);   (*  2^{29} *)
IntToSup (65539, aa);
TestIt (4);

IntToSup (1073741824, mm);  MultiplyIntSup (2, mm, mm);   (*  2^{32}  *)
IntToSup (69069, aa);
TestIt (5);

IntToSup (4096 * 4096, mm);  Multiply (mm, mm, mm);        (*  2^{48}  *)
IntToSup (1108835251, aa);
TestIt (6);
*)
FOR i := t1 TO t2 DO
   WriteLn;
   WriteString (" $S_");  WriteInt (i, 1);  WriteString ("$ ");
   FOR j := 1 TO 2 DO  
      WriteString (" & ");  WriteLR (SaveS [j, i], 9, 4, 3);  
      END;
   WriteString (" \\");
   END;
WriteLn;
FOR i := t1 TO t2 DO
   WriteLn;
   WriteString (" $d_{");  WriteInt (i, 1);  WriteString ("}$ ");
   FOR j := 1 TO 2 DO  
      WriteString (" & ");  WriteLR (SaveD [j, i], 9, 4, 3);  
      END;
   WriteString (" \\");
   END;
WriteLn;

END tab1.


