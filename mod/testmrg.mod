MODULE testmrg;
(* This program assumes the representation LI LR  *)

FROM LATBASIS IMPORT Basis, WriteBasis, CreateBasis, InitBasis;
FROM REDBAS   IMPORT InitREDBAS;
FROM REDBAS2  IMPORT InitREDBAS2;
FROM MRG      IMPORT TestType, VerifyType, Test, InitMRG,
                     BuildBasis, NormalG;
FROM MULT     IMPORT MAffect, MScal, MVect, MCreateScal, MCreateVect;
FROM CONFIG   IMPORT OutputType, MDim, BDim;
FROM CONVERT  IMPORT SupToMScal;
FROM SUPINT   IMPORT SuperInteger, Create;
FROM SUPCONV  IMPORT IntToSup;
FROM SUPARITH IMPORT Multiply, MultiplyIntSup;
FROM MYINOUT  IMPORT WriteString, WriteInt, WriteLn;
FROM NUM      IMPORT WriteLR;
FROM NORM     IMPORT GammaType, NormType, InitNormaliz;

VAR
   aa, mm : SuperInteger;
   v      : MVect;
   m, a   : MScal;
   i, j, t1, t2 : BDim;
   B :Basis;


BEGIN
Create (mm, 2);
Create (aa, 2);
MCreateScal (m);
MCreateVect (v, 0, 5);
(*
m := 2147483647;
m := 32749;
t1 := 2;  t2 := 3;
v[0] := 16807;
v[1] := 7521;
*)
m := 101;
t1 := 2;  t2 := 2;

v[0] := 7;
InitNormaliz (NormalG, L2Norm, BestLat, m, 1, 1.0);
InitMRG (m, 1, t2);
Test (v, Spectral, t1, t2, Verify0, CurOut); 

v[0] := 12;
InitNormaliz (NormalG, L2Norm, BestLat, m, 1, 1.0);
InitMRG (m, 1, t2);
Test (v, Spectral, t1, t2, Verify0, CurOut); 

v[0] := 51;
InitNormaliz (NormalG, L2Norm, BestLat, m, 1, 1.0);
InitMRG (m, 1, t2);
Test (v, Spectral, t1, t2, Verify0, CurOut); 

HALT;
CreateBasis (B);
InitBasis (B, m, L2Norm, t2);
BuildBasis(B, v, t2);
WriteBasis (B);
END testmrg.


