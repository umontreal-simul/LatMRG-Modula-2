(* Revision du code : Benoit Martin, Mars 1995 *)
MODULE select;

FROM MYINOUT   IMPORT ReadLine, ReadLn, WriteString, WriteLn, OpenAsInput,
 		      OpenAsOutput, CloseInput, CloseOutput,  EOF, FILE,
                      GetInput, GetOutput;
FROM MYPARAM   IMPORT ParamToString;
FROM MYSTR     IMPORT Concat, Subst, Caps, Match, Length;


CONST
   Path        = './';
   (*   Path        = '/home/rapide/stochas/latmrg/xds99/';   *)
   BasisyyDef  = 'BASISyy.def';
   BasisyyMod  = 'BASISyy.mod';
   MultxxDef   = 'MULTxx.def';
   MultxxMod   = 'MULTxx.mod';
   xxyyDef     = 'xxyy.def';
   xxyyMod     = 'xxyy.mod';
   DefBasisyy  = 'DEFINITION MODULE BASISyy;';
   ImpBasisyy  = 'IMPLEMENTATION MODULE BASISyy;';
   EndBasisyy  = 'END BASISyy.';
   DefMultxx   = 'DEFINITION MODULE MULTxx;';
   ImpMultxx   = 'IMPLEMENTATION MODULE MULTxx;';
   EndMultxx   = 'END MULTxx.';
   Defxxyy     = 'DEFINITION MODULE xxyy;';
   Impxxyy     = 'IMPLEMENTATION MODULE xxyy;';
   Endxxyy     = 'END xxyy.';
   FromMultxx  = 'FROM MULTxx';
   FromBasisyy = 'FROM BASISyy';
   BasisDef    = 'BASIS.def';
   BasisMod    = 'BASIS.mod';
   MultDef     = 'MULT.def';
   MultMod     = 'MULT.mod';
   ConvertDef  = 'CONVERT.def';
   ConvertMod  = 'CONVERT.mod';
   DefBasis    = 'DEFINITION MODULE BASIS;';
   ImpBasis    = 'IMPLEMENTATION MODULE BASIS;';
   EndBasis    = 'END BASIS.';
   DefMult     = 'DEFINITION MODULE MULT;';
   ImpMult     = 'IMPLEMENTATION MODULE MULT;';
   EndMult     = 'END MULT.';
   DefConvert  = 'DEFINITION MODULE CONVERT;';
   ImpConvert  = 'IMPLEMENTATION MODULE CONVERT;';
   EndConvert  = 'END CONVERT.';
   FromMult    = 'FROM MULT    IMPORT MScal;';
   FromBasis   = 'FROM BASIS   IMPORT BScal;';


VAR
   f      : ARRAY [0..50] OF CHAR;
   s      : ARRAY [0..100] OF CHAR;
   xxyy   : ARRAY [0..3] OF CHAR;
   xx,yy  : ARRAY [0..2] OF CHAR;
   fchin,
   fchout : FILE;


PROCEDURE ChainsEqual
   ( s1,
     s2 : ARRAY OF CHAR;
     k  : CARDINAL
     ) : BOOLEAN;
   VAR
      j : CARDINAL;
   BEGIN
   FOR j := 0 TO k-1 DO
      IF s1[j] # s2[j] THEN RETURN FALSE END
      END;
   RETURN TRUE
   END ChainsEqual;


PROCEDURE Error
   ( s,
     f : ARRAY OF CHAR
     );
   BEGIN
   CloseInput; CloseOutput;
   WriteString ("Error! '");
   WriteString (s);
   WriteString ("' is not present in '");
   WriteString (f);
   WriteString ("'");
   WriteLn;
   HALT
   END Error;


PROCEDURE TrouverChaine
   ( s1,                         (* chaine a remplacer       *)
     s2 ,                        (* chaine qui remplace s1   *)
     f   : ARRAY OF CHAR;        (* nom du fichier           *)
     Long : CARDINAL             (* longueur de la chaine    *)
     );
   VAR
      Trouve : BOOLEAN;
      s      : ARRAY [0..100] OF CHAR;
   BEGIN
   Trouve := FALSE;
   ReadLine (s);
   WHILE ( NOT EOF () ) AND ( NOT Trouve ) DO
      ReadLn;
      Trouve := ChainsEqual(s,s1,Long);
      IF NOT Trouve THEN WriteString(s); WriteLn; ReadLine (s) END;
      END;
   IF Trouve THEN
      WriteString(s2); WriteLn
   ELSE
      Error (s1, f)
      END
   END TrouverChaine;



PROCEDURE ErrorP;
   BEGIN
   CloseInput; CloseOutput;
   WriteString ('Error in parameters'); WriteLn;
   HALT
   END ErrorP;


BEGIN
ParamToString (1, xx); ParamToString (2, yy);
Caps (xx); Caps (yy);
Concat (xxyy, xx, yy);
IF NOT ( Match (xxyy, 'SISI') OR Match (xxyy, 'SILR') OR Match (xxyy, 'LILR')
         OR Match (xxyy, 'LISI')) THEN ErrorP END;

(* Conversion de MULTxx.DEF ----> MULT.DEF *)
   (* Ouverture des fichiers *)
   Concat ( f, Path, MultxxDef );
   Subst  ( f , 'xx' ,xx);
   OpenAsInput (f);
   GetInput (fchin);

   Concat (f, Path, MultDef); 
   OpenAsOutput (f);
   GetOutput (fchout);

   Concat ( f, Path, MultxxDef );
   Subst  ( f , 'xx' ,xx);

   (* Trouver la chaine ( DEFINTION... ou IMPLEMENTAION... *)
   s := DefMultxx; Subst (s, 'xx', xx);
   TrouverChaine ( s, DefMult, f, Length(DefMultxx));

   (* Trouver la chaine ( END ... ) *)
   s := EndMultxx; Subst (s, 'xx', xx);
   TrouverChaine ( s, EndMult, f, Length(EndMultxx));

   (* Fermerture des fichiers *)
   CloseInput; CloseOutput;
 
(* Conversion de MULTxx.MOD ----> MULT.MOD *)
   (* Ouverture des fichiers *)
   Concat ( f, Path, MultxxMod );
   Subst  ( f, 'xx', xx);
   OpenAsInput (f);
   GetInput (fchin);
   Concat ( f, Path, MultMod );
   OpenAsOutput (f);
   GetOutput (fchout);

   (* Trouver la chaine ( DEFINTION... ou IMPLEMENTAION... *)
   s := ImpMultxx; Subst  (s, 'xx', xx);
   TrouverChaine ( s, ImpMult, f, Length(ImpMultxx));

   (* Trouver la chaine ( END ... ) *)
   s := EndMultxx; Subst  (s, 'xx', xx);
   TrouverChaine ( s, EndMult, f, Length(EndMultxx));

   (* Fermerture des fichiers *)
   CloseInput; CloseOutput;


(* Conversion de BASISyy.DEF ----> BASIS.DEF *)
   (* Ouverture des fichiers *)
   Concat ( f, Path, BasisyyDef );
   Subst  ( f, 'yy', yy);
   OpenAsInput (f);
   GetInput (fchin);
   Concat ( f, Path, BasisDef );
   OpenAsOutput (f);
   GetOutput (fchout);

   (* Trouver la chaine ( DEFINTION... ou IMPLEMENTAION... *)
   s := DefBasisyy; Subst  ( s, 'yy', yy);
   TrouverChaine ( s, DefBasis, f, Length(DefBasisyy));

   (* Trouver la chaine ( END ... ) *)
   s := EndBasisyy; Subst  ( s, 'yy', yy);
   TrouverChaine ( s, EndBasis, f, Length(EndBasisyy));

   (* Fermerture des fichiers *)
   CloseInput; CloseOutput;

(* Conversion de BASISyy.MOD ----> BASIS.MOD *)
   (* Ouverture des fichiers *)
   Concat ( f, Path, BasisyyMod );
   Subst  ( f, 'yy', yy);
   OpenAsInput (f);
   GetInput (fchin);
   Concat ( f, Path, BasisMod );
   OpenAsOutput (f);
   GetOutput (fchout);

   (* Trouver la chaine ( DEFINTION... ou IMPLEMENTAION... *)
   s := ImpBasisyy; Subst  ( s, 'yy', yy);
   TrouverChaine ( s, ImpBasis, f, Length(ImpBasisyy));

   (* Trouver la chaine ( END ... ) *)
   s := EndBasisyy; Subst  ( s, 'yy', yy);
   TrouverChaine ( s, EndBasis, f, Length(EndBasisyy));

   (* Fermerture des fichiers *)
   CloseInput; CloseOutput;


(* Conversion de xxyy.DEF ----> CONVERT.DEF *)
   (* Ouverture des fichiers *)
   Concat ( f, Path, xxyyDef );
   Subst  ( f, 'xxyy', xxyy);
   OpenAsInput (f);
   GetInput (fchin);
   Concat ( f, Path, ConvertDef );
   OpenAsOutput (f);
   GetOutput (fchout);

   (* Trouver la chaine ( DEFINTION... ou IMPLEMENTAION... *)
   s := Defxxyy; Subst  ( s, 'xxyy', xxyy);
   TrouverChaine ( s, DefConvert, f, Length(Defxxyy));

   (* Trouver la chaine ( FROM MULTxx ....) *)
   s := FromMultxx; Subst  ( s, 'xx', xx);
   TrouverChaine ( s, FromMult, f, Length(FromMultxx));

   (* Trouver la chaine ( FROM BASISyy ...) *)
   s := FromBasisyy; Subst  ( s, 'yy', yy);
   TrouverChaine ( s, FromBasis, f, Length(FromBasisyy));

   (* Trouver la chaine ( END ... ) *)
   s := Endxxyy; Subst  ( s, 'xxyy', xxyy);
   TrouverChaine ( s, EndConvert, f, Length(Endxxyy));

   (* Fermerture des fichiers *)
   CloseInput; CloseOutput;


(* Conversion de xxyy.MOD ----> CONVERT.MOD *)
   (* Ouverture des fichiers *)
   Concat ( f, Path, xxyyMod );
   Subst  ( f, 'xxyy', xxyy);
   OpenAsInput (f);
   GetInput (fchin);
   Concat ( f, Path, ConvertMod );
   OpenAsOutput (f);
   GetOutput (fchout);
 
   (* Trouver la chaine ( DEFINTION... ou IMPLEMENTAION... *)
   s := Impxxyy; Subst  ( s, 'xxyy', xxyy);
   TrouverChaine ( s, ImpConvert, f, Length(Impxxyy));

   (* Trouver la chaine ( FROM MULTxx ....) *)
   s := FromMultxx; Subst  ( s, 'xx', xx);
   TrouverChaine ( s, FromMult, f, Length(FromMultxx));

   (* Trouver la chaine ( FROM BASISyy ...) *)
   s := FromBasisyy; Subst  ( s, 'yy', yy);
   TrouverChaine ( s, FromBasis, f, Length(FromBasisyy));

   (* Trouver la chaine ( END ... ) *)
   s := Endxxyy; Subst  ( s, 'xxyy', xxyy);
   TrouverChaine ( s, EndConvert, f, Length(Endxxyy));

   (* Fermerture des fichiers *)
   CloseInput; CloseOutput;

END select.



