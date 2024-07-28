MODULE testlatbasis;

FROM CONFIG    IMPORT MDim, BDim, DimProj, MCoord, Categ;
FROM MULT      IMPORT MScal, MCreateScal, MDeleteScal, LIToMScal;
FROM MYINOUT   IMPORT WriteString, WriteLn;
FROM NORM      IMPORT NormType;
FROM BASIS     IMPORT LIToBScal;
FROM LATBASIS  IMPORT Basis, CreateBasis, InitBasis, DeleteBasis, WriteBasis,
                      ReadBasis, CopyBasis, Permute, SortBasis, Dualize,
                      UpdateVVWW, EraseVVWW, CheckDuality, BaseEquivalence;

CONST
   separ = "------------------------------------------ ";

VAR
   m : MScal;
   B, B2 : Basis;
   i, j, dim :BDim;

BEGIN
MCreateScal (m);
LIToMScal (101, m);

WriteString (separ);
WriteString ("CreateBasis"); WriteLn;
CreateBasis (B);
CreateBasis (B2);

dim := 4;
B^.Dim := dim;

WriteString (separ);
WriteString ("InitBasis "); WriteLn;
InitBasis (B, m, L2Norm, dim);
InitBasis (B2, m, L2Norm, dim);

FOR i := 1 TO dim DO
   FOR j := 1 TO dim DO
	LIToBScal (i+j, B^.V[i,j]);
	LIToBScal (i+j + 10, B^.W[i,j]);
      END;
   END;
WriteBasis (B);
IF CheckDuality (B) THEN END;
(*
WriteString (separ);
WriteString ("CopyBasis  "); WriteLn;
CopyBasis (B, B2);
WriteBasis (B2);

WriteString (separ);
WriteString ("Permute 1 3"); WriteLn;
Permute (B, 1, 3);
WriteBasis (B);

WriteString (separ);
WriteString ("UpdateVVWW "); WriteLn;
UpdateVVWW (B, 0);
WriteBasis (B);

WriteString (separ);
WriteString ("SortBasis "); WriteLn;
SortBasis (B, 0);
WriteBasis (B);

WriteString (separ);
WriteString ("Dualize "); WriteLn;
Dualize (B);
WriteBasis (B);

WriteString (separ);
WriteString ("EraseVVWW "); WriteLn;
EraseVVWW (B);
WriteBasis (B);
*)
(* Pour lire une base,
	 testlatbasis < base.dat
   le fichier de donnees base.dat doit avoir ete ecrit par WriteBasis
*)

WriteString (separ);
WriteString ("ReadBasis "); WriteLn;
ReadBasis (B);
WriteString (separ);
WriteString ("WriteBasis "); WriteLn;
WriteBasis (B);

WriteString (separ);
WriteString ("CheckDuality B"); WriteLn;
IF CheckDuality (B) THEN END;

WriteString (separ);
WriteString ("ReadBasis "); WriteLn;
ReadBasis (B2);
WriteString (separ);
WriteString ("WriteBasis "); WriteLn;
WriteBasis (B2);

WriteString (separ);
WriteString ("CheckDuality B2 "); WriteLn;
IF CheckDuality (B2) THEN END;

WriteString (separ);
WriteString ("BaseEquivalence B, B2"); WriteLn;
IF BaseEquivalence (B, B2) THEN END;

WriteString (separ);
WriteString ("DeleteBasis "); WriteLn;

DeleteBasis (B);
DeleteBasis (B2);
MDeleteScal (m);

END testlatbasis.
