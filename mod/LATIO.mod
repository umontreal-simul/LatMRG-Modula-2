<* +M2EXTENSIONS *>

IMPLEMENTATION MODULE LATIO;

(****************************************************************************)
(*  Programmeurs : Pierre L'Ecuyer, Marco Jacques, Josee Turgeon            *)
(*  ------------                                                            *)
(****************************************************************************)

(*# data ( stack_size => 5000H, heap_size  => 100) *)

FROM Storage  IMPORT ALLOCATE, DEALLOCATE;
FROM SYSTEM   IMPORT CAST;
FROM NUM      IMPORT Sqrt, Round, WriteLI, WriteLR, ReadLR, LIToLR, IToLI,
                     IToLR;
FROM MYINOUT  IMPORT ReadBool, ReadInt, ReadLine, ReadString, ReadLongInt,
                     ReadLn, WriteString, WriteLn, WriteInt, EOF, FILE,
                     GetInput, GetOutput, SetInput, SetOutput, CloseInput,
                     CloseOutput, OpenAsInput, OpenAsOutput;
FROM MYSTR    IMPORT Match, ItemS, Concat, StrToInt;
FROM MYPARAM  IMPORT ParamToString, HostName;
FROM CHRONO   IMPORT Chrono, TimeFormat, ValChrono, InitChrono, WriteChrono;

<* IF XDSV = "99" THEN *>
   FROM RAND     IMPORT RandU01, RngStream, CreateStream;
<* ELSE *>
   FROM RAND     IMPORT Uniform01;
   <* END *>


FROM SUPINT   IMPORT Affect, Create, Delete, SuperInteger, ReadSup, WriteSup;
FROM SUPARITH IMPORT Add, Greater, Equal, Positive, PowerSupInt, ChangeSign,
                     Negative, Subtract, Quotient, GCD, Modulo, Multiply,
                     MultMod, PowerMod, Smaller, MultiplyIntSup, Divide,
                     DivideSupInt, Euclide;
FROM SUPCONV  IMPORT IntToSup, SupToInt, SupToLongReal, RoundLongRealToSup;
FROM SUPRAND  IMPORT SetSeed, SupRandom;
FROM SUPFACT  IMPORT Factors, IsPrime;

IMPORT BASISLR, BASIS;
FROM BASIS    IMPORT BReadScal, BCreateVect;
FROM CONFIG   IMPORT OutputType, MDim, MMaxDim, BDim, BMaxDim, Indexj, MaxJ,
                     Categ, MaxNbGen;
FROM CONVERT  IMPORT MScalToSup, SupToMScal, SupToBScal;
FROM MULT     IMPORT MScal, MVect, MReadScal,
                     MCreateScal, MCreateVect, MWriteScalBin,
                     MWriteScal, SetFactors, PrimElem, MaxPeriod, MCopyVect,
                     MAffect, MWriteVect, MPowerLI, MZero, MOne, MTwo, 
                     MEqual, MInc, MAdd, MSubtract, MSmaller, MQuotient, 
                     MMultiply, MModulo, MSetm, LIToMScal;
FROM NORM     IMPORT NormType, CriterionType, GammaType, CreateNormaliz, 
                     InitNormaliz, Normaliz;
FROM REDBAS   IMPORT VerifyType, MaxNodesBB, InitREDBAS;
FROM REDBAS2  IMPORT InitREDBAS2;
FROM MRG      IMPORT InitMRG, Test, TestLa, LatticeType, LatType, InSta,
                     Lacunary, Mins2, Minq2, UsedNorm, DualLattice, NormalG,
                     Q2, S2, D2, InvertCrit, TestCompleted, Bas;




CONST
   MaxZones    = 3;                 (* Nb. max de zones pour un (j,i).       *)
   Espace      = ' 	';          (* Blank and TAB.                        *)
   MaxHighBit  = 63;                (* Upper bound on HighestBit.            *)

TYPE
   ResForm     = (LTerminal, STerminal, RES, GEN, RESGEN, TEX);
   ResFormSeek = [STerminal..RESGEN];
   Decompr     = (Decomp, DecompWrite, READ, Prime);
   DecompmMS1  = [Decomp..READ];
   ProcII      = PROCEDURE (INTEGER, INTEGER);

VAR
   Order, J     : INTEGER;           (* Ordre et nb. compos. du gen. combin. *)
   m            : MScal;             (* Le modulo du generateur combine.     *)
   a            : MVect;             (* Les coefficients de la recurrence    *)
                                     (* pour le gener. combine.              *)
   mm, mmN      : SuperInteger;      (* m_j et -m_j (variables de lecture.)  *)
   mRed         : MScal;             (* Le modulo reduit, cas PrimePower.    *)
   Rho, LossRho : SuperInteger;      (* Period length lcm (rho_j) and        *)
                                     (* prod (rho_j) / lcm (rho_j).          *)

   (* Pour chaque composante d'un generateur combine:                        *)
   TypeGen              : ARRAY Indexj OF GenerType;
   mj, mjRed            : ARRAY Indexj OF SuperInteger;
   mjm2, mSurmj, nj     : ARRAY Indexj OF SuperInteger;
   mRac, mRacNeg        : ARRAY Indexj OF SuperInteger; (* +/- Sqrt (m_j)    *)
   aj, bj, cj           : ARRAY Indexj OF ARRAY MDim OF SuperInteger;
      (* Les aj [j,i] sont multiplicateurs que l'on examine et les bj et cj  *)
      (* donnent les bornes inf et sup sur ces multiplicateurs pour seek.    *)
   Mmj                  : ARRAY Indexj OF MScal;  (* = m_j                   *)
   Maj                  : ARRAY Indexj OF MVect;  (* = a_j                   *)
   Orderj               : ARRAY Indexj OF INTEGER; (* Order of component j   *)
   PerMax               : ARRAY Indexj OF BOOLEAN; (* Si on exige period max.*)
   Primemj              : ARRAY Indexj OF BOOLEAN; (* If TRUE, then m_j is   *)
                                     (*    assumed prime and PerMax is true. *)
   Rhoj                 : ARRAY Indexj OF SuperInteger; (* Period of comp. j *)
   ListPoly             : ARRAY Indexj OF Poly; (* List of prim. polynomials.*)
   DecomposeR           : ARRAY Indexj OF Decompr;
   DecomposeM           : ARRAY Indexj OF DecompmMS1;
   EcriremMS1, Ecrirer  : ARRAY Indexj OF BOOLEAN;
   FactmMS1, Factr      : ARRAY Indexj OF Factors;
   ImplemCond           : ARRAY Indexj OF CondType; (* Type de cond. implem. *)
   NbMaxBits, HighestBit : ARRAY Indexj OF INTEGER; (* For MaxBits.          *)
   Exhaust              : ARRAY Indexj OF BOOLEAN; (* Exaustive search.      *)
   TroisChiffres        : ARRAY Indexj OF BOOLEAN; (* m_j read as 3 integers *)
   M1, M2, M3           : ARRAY Indexj OF LONGINT; (* If TroisChiffres [j],  *)
                                     (* then,  m_j = M1[j]^M2[j] + M3[j].    *)
   bcZone               : ARRAY Indexj OF ARRAY MDim OF ToZone;
      (* Pointeur sur la premiere des zones retenues, pour chaque [j,i].     *)
   Frontiere            : ARRAY Indexj OF ARRAY [1..MaxZones] OF SuperInteger;
      (* Frontiere sup de chaque zone: -sqrt{m_j}-1, sqrt{m_j}, m_j-1.       *)
   DivQ                 : ARRAY [0..MaxZones] OF BOOLEAN;
      (* Si TRUE, on cherche des multiplicateurs m/a dans cette zone avec    *)
      (* a entre les bornes.  TRUE pour les zones 1 et 3.                    *)
   NbReg, H, Hk         : ARRAY Indexj OF LONGINT;
      (* NbReg = Nb de regions a tirer au hasard pour chaque a[j,i].         *)
      (* H et Hk determinent la taille de ces regions.                       *)
   Reg                  : ARRAY Indexj OF ARRAY MDim OF ToRegion;
      (* Pointeur sur la region choisie (a fouiller) pour recherche aleat.   *)

   Seek                 : BOOLEAN;   (* Whether a seek is performed or not. *)
   Criterion            : CriterionType; (* Critere de selection des generat.*)
   MinMerit, MaxMerit   : BASISLR.BVect;
      (* Seuils de retention (pour le critere), par categorie.              *)
   MinDim, MaxDim       : INTEGER;   (* On teste dans cette plage de dimens.*)
   LacI                 : BASIS.BVect; (* Vector of lacunary indices.       *)
   ResultForm           : ResForm;
   LatInfo              : CriterionType; (* Information a imprimer.         *)
   Verif                : VerifType; (* Indique ce qu'il faut verifier.     *)
   VerifyAll, VerifyRet : VerifyType; (*   "              "       "         *)
   Seed1, Seed2         : LONGINT;   (* Seeds for RNG pour recherche aleat. *)

   ReadGenFromFile      : BOOLEAN;
      (* TRUE ssi on lit les generateurs a analyser dans un fichier.        *)
   NbGenFile            : INTEGER;   (* Nb. de gener. a lire dans fichier.  *)
                                     (* Ce nombre est une borne superieure  *)
                                     (* dans le cas de multiples dimensions *)
   CptElemPrim,                      (* Nb de A_k  elem. primitif.          *)
   CptPerMax,                        (* Nb de gen. avec periode maximale.   *)
   CptNoElemPrim,
   CptRegions,                       (* Nb de sous-regions testees.        *)
   TotGen,                           (* Nb total de gen. examines.         *)
   TotEP                             (* Nb de gen. avec A_k elem. primit.  *)
                  : ARRAY Indexj OF LONGINT;
   ApproxTotGen   : ARRAY Indexj OF BOOLEAN;
      (* TRUE si recherche aleatoire et + d'une zone pour une composante.  *)
      (* nb affiche de gen. examines sera alors approximatif.              *)
   Timer2         : Chrono;
   TempsLimite    : LONGREAL;        (* CPU Time limit.                    *)
   TropLong       : BOOLEAN;         (* Mis a TRUE lorsque "TimeLimit".    *)

   i                                  : INTEGER;
   SupT, SupT1, SupT2, SupT3          : SuperInteger;
   Eb, Ec, E, h, P, Pm1, P2, Tot      : SuperInteger;
   Sa, VectSup                        : ARRAY MDim OF SuperInteger;
   Str1, Str2, Str3                   : ARRAY [0..100] OF CHAR;
   MTemp, MTemp1, MTemp2, MTemp3, MTemp4        : MScal;
   MThree, MFour, MFive, MSeven, MEight         : MScal;
   Zero, One, Two, Four, Five, Eight, DixExp50  : SuperInteger;
   FName, S                           : ARRAY [0..100] OF CHAR;
   FichGen                            : ARRAY [0..30] OF CHAR;
                                        (* Fichiers des generateurs.      *)
   FichmMS1, Fichr                    : ARRAY Indexj OF ARRAY [0..30] OF CHAR;
                                        (* Fichiers de decompos. en fact. *)
   (* FIn, FOut, *) stdIn, stdOut     : FILE; 
   Out                                : OutputType;
   Tex                                : BOOLEAN;
   MTwoExp                            : ARRAY [0..MaxHighBit] OF MScal;
                                        (* Powers of 2, used for MaxBits.  *)

   (*  Pour traiter plusieurs dimensions en meme temps.                    *)
   Maxs2, Maxq2 : BASISLR.BVect;
   NbCat        : LONGINT;
   MaxAllCat    : BOOLEAN;                 (* If all MaximCat [C] = TRUE.  *)
   TabDim  : ARRAY Categ OF LONGINT;       (* Indices de fin des categor.  *)
   MaximCat: ARRAY Categ OF BOOLEAN;       (* Vrai si on maximise le merite*)
   PireGen : ARRAY Categ OF Generateur;    (* Pointeurs sur les listes. *)
   NbGen   : ARRAY Categ OF INTEGER;       (* Nb de gener. a retenir dans  *)
                                           (* les differentes categoties.  *)
   NbTried : ARRAY Categ OF INTEGER;       (* Nb de gener. essayes.        *)
   Caff    : ARRAY Categ OF LONGINT;       (* Nb. de Gen. retenus.         *)
   Streams : BOOLEAN ;                  (* Vrai lorsque latclcgs est utilise*)

<* IF XDSV = "99" THEN *>
   RngBornes : RngStream;             (* Random Numbers stream pour Bornes *)
   <* END *>

   Critere2 : GammaType;




(*****************************************************************************)
(*
PROCEDURE Message (S : ARRAY OF CHAR);
   (* Affiche un message sur une ligne.   *)
   BEGIN
   WriteString (' ** Message LATIO: ');
   WriteString (S);   WriteString (' **');   WriteLn;
   END Message;
*)
(****************************************************************************)

PROCEDURE ErrorHalt (S : ARRAY OF CHAR);
   (* Affiche un message d'erreur et arrete le programme.  *)
   BEGIN
   WriteString (' **** ERROR LATIO: ');
   WriteString (S);   WriteString (' ****');   WriteLn;   HALT
   END ErrorHalt;

(****************************************************************************)
(*
PROCEDURE ErrorHalt2 (S1, S2 : ARRAY OF CHAR);
   (* Affiche deux messages d'erreur et arrete le programme.  *)
   BEGIN
   WriteString (' **** ERROR LATIO: ');   WriteString (S1);
   WriteString (S2);   WriteString (' ****');   WriteLn;   HALT
   END ErrorHalt2;
*)
(****************************************************************************)

PROCEDURE ErreurChamp (S : ARRAY OF CHAR);
   (* Indique une erreur dans le fichier de donnees.  *)
   BEGIN
   WriteString (' **** ERROR LATIO: Wrong data in field ');
   WriteString (S);   WriteString (' ****');   WriteLn;   HALT
   END ErreurChamp;

(****************************************************************************)

PROCEDURE TimeOver () : BOOLEAN;
   (* Returne TRUE ssi le temps limite de cpu est atteint.                  *)
   BEGIN
   IF ValChrono (Timer2, hours) > TempsLimite THEN
      TropLong := TRUE;  RETURN TRUE
   ELSE RETURN FALSE  END
   END TimeOver;

(****************************************************************************)

PROCEDURE CreatePoly (VAR P : Poly;  j : Indexj);
   (* Ajoute un polynome dans la liste des poly. retenus pour la compos. j  *)
   BEGIN
   NEW (P);
   WITH P^ DO
      MCreateVect (a, 0, Order);
      NextPoly := ListPoly [j];   ListPoly [j] := P
      END
   END CreatePoly;

(****************************************************************************)

PROCEDURE CreateGenerateur (VAR G : Generateur);
   (* Cree un generateur G.  *)
   VAR
      jj : INTEGER;
   BEGIN
   NEW (G);
   WITH G^ DO
      NextGen := NIL;  Merit := 0.0;  DimMerit := 0;
      MCreateVect (a, 0, Order);
      FOR jj := 1 TO J DO  MCreateVect (Maj [jj], 0, Orderj [jj])  END;
      IF ResultForm # GEN THEN  NEW (Res)  END
      END
   END CreateGenerateur;

(****************************************************************************)

PROCEDURE CreateZone (VAR Z : ToZone);
   (* Cree une zone Z.  *)
   BEGIN
   NEW (Z);
   WITH Z^ DO
      No := 0;  NextZone := NIL;   MCreateScal (Mq);  MCreateScal (MBsup);
      Create (Binf, 4);  Create (Bsup, 4);  Create (BsupMsH, 4);
      END
   END CreateZone;

(****************************************************************************)

PROCEDURE CreateRegion (VAR R : ToRegion);
   (*  Cree une region R.   *)
   BEGIN
   NEW (R);
   WITH R^ DO
      No := 0;  MCreateScal (Mq);  MCreateScal (Binf);  MCreateScal (Bsup)
      END
   END CreateRegion;

(****************************************************************************)

PROCEDURE LireFact (VAR L : Factors;   NomFch : ARRAY OF CHAR);
   (* Lit une liste de facteurs dans NomFch et les place dans la liste L.   *)
   (* Suppose (pour le format) qu'ils ont ete ecrits par EcrireFact.        *)
   VAR
      FirstFact : BOOLEAN;             (* TRUE si facteur 1 pas encore lu. *)
      F         : Factors;
      in0       : FILE;
      Fact, PrecFact : SuperInteger;
   BEGIN
   GetInput (in0);   OpenAsInput (NomFch);   (*  GetInput (FIn);  *)
   FirstFact := TRUE;   Create (Fact, 2);   Create (PrecFact, 2);
   (* PrecFact = 0.   *)
   ReadSup (Fact, 10);
   WHILE NOT EOF () DO
      ReadLn;
      IF FirstFact THEN
         NEW (L);  F := L;  FirstFact := FALSE
      ELSE
         NEW (F^.Next);   F := F^.Next
         END;
      WITH F^ DO
         Create (Factor, 2);  Affect (Fact, Factor);
         Multiplicity := 1;
         ReadSup (PrecFact, 10);
         (* Lire les facteurs repetes. *)
         WHILE Equal (Fact, PrecFact) DO
            ReadLn;  INC (Multiplicity);  ReadSup (PrecFact, 10);
            END;
         Affect (PrecFact, Fact);
         END;
      END;
   F^.Next := NIL;
   CloseInput;   SetInput (in0);   Delete (Fact);  Delete (PrecFact)
   END LireFact;

(*****************************************************************************)

PROCEDURE EcrireFact (L : Factors;   NomFch : ARRAY OF CHAR);
   (* Ecrit les facteurs de la liste L dans NomFch.                         *)
   (* Si le fichier existe, le remplace.                                    *)
   VAR
      pow : LONGCARD;   out0 : FILE;
   BEGIN
   GetOutput (out0);   OpenAsOutput (NomFch);  (*   GetOutput (FOut);  *)
   WHILE L # NIL DO
      pow := L^.Multiplicity;
      REPEAT				 (* Ecrit tous les facteurs repetes *)
         WriteSup (L^.Factor, 10, 70);   WriteLn;   DEC (pow)
      UNTIL  pow = 0;
      L := L^.Next
      END;
   CloseOutput;   SetOutput (out0);
   END EcrireFact;

(****************************************************************************)

PROCEDURE Readm (j : Indexj);
   (* Lit le modulo m_j pour la composante j.                             *)
   (* Initialise mj[j], mRac[j], mRacNeg[j].                              *)
   VAR
      Done, Done1 : BOOLEAN;
      s2, s3 : LONGINT;
      Temp   : LONGREAL;
   BEGIN
   ReadSup (mm, 10);   ReadLine (S);   ReadLn;
   ItemS (Str2, S, Espace, 0);    s2 := StrToInt (Str2, 10, Done);
   ItemS (Str3, S, Espace, 1);    s3 := StrToInt (Str3, 10, Done1);
   IF Done AND Done1 THEN		  (* il y a trois chiffres *)
      IF (NOT Greater (mm, Zero)) OR (s2 < 0) THEN ErreurChamp (' m ') END;
      SupToInt (mm, M1 [j]);  M2 [j] := s2;  M3 [j] := s3;
      TroisChiffres [j] := TRUE;
      PowerSupInt (mm, s2, mm);   IntToSup (s3, SupT);   Add (mm, SupT, mm);
   ELSE                                   (* un seul chiffre       *)
      TroisChiffres [j] := FALSE
      END;
   Affect (mm, mj [j]);   ChangeSign (mm, mmN);
   IF Seek THEN
      (* On veut  mRac [j] := Trunc (Sqrt (mm)).  C'est pour AppFact.      *)
      (* Attention, ici, il peut y avoir perte de precision...             *)
      Create (mRac [j], 2);   SupToLongReal (mm, Temp);   Temp := Sqrt (Temp);
      RoundLongRealToSup (Temp - 0.5, mRac [j]);
      ChangeSign (mRac [j], mRacNeg [j]);
      END
   END Readm;

(*********************************************************************)

PROCEDURE ReadOnea (aa : SuperInteger);
   (* Lit un multiplicateur a (ou une borne b ou c).                 *)
   VAR
      s2, s3      : LONGINT;
      Done, Done1 : BOOLEAN;
      Negatif     : BOOLEAN;
   BEGIN
   ReadSup (aa, 10);   ReadLine (S);   ReadLn;
   ItemS (Str2, S, Espace, 0);    s2 := StrToInt (Str2, 10, Done);
   ItemS (Str3, S, Espace, 1);    s3 := StrToInt (Str3, 10, Done1);
   IF Done AND Done1 THEN		     (* il y a trois chiffres *)
      IF s2 < 0 THEN ErreurChamp (" a, b, ou c "); END;
      Negatif := Negative (aa);
      IF Negatif THEN  ChangeSign (aa, aa) END;
      PowerSupInt (aa, s2, aa);   IntToSup (s3, SupT);   Add (aa, SupT, aa);
      IF Negatif THEN  ChangeSign (aa, aa) END
      END;
   END ReadOnea;

(*********************************************************************)

PROCEDURE ReadReadGen;
   BEGIN
   ReadLine (S);   ReadLn;   ItemS (Str1, S, Espace, 0);
   ReadGenFromFile := (Match (Str1, 'TRUE') OR Match (Str1, 'true'));
   IF ReadGenFromFile THEN ItemS (FichGen, S, Espace, 1) END;
   END ReadReadGen;

(*********************************************************************)

PROCEDURE ReadTypeGen (j : Indexj);
   BEGIN
   ReadLine (S);   ReadLn;   ItemS (Str1, S, Espace, 0);
   IF Match (Str1, 'MRG') THEN  
      TypeGen [j] := MRG
   ELSIF Match (Str1, 'MWC') THEN  
      TypeGen [j] := MWC
   ELSE
      ErreurChamp (' ReadTypeGen ')
      END
   END ReadTypeGen;

(*********************************************************************)

PROCEDURE ReadOrder (j : Indexj);
   BEGIN
   ReadInt (Orderj [j]);
   IF (Orderj [j] < 1) OR (Orderj [j] > MMaxDim) THEN
      ErreurChamp (' k ')
      END;
   ReadLn
   END ReadOrder;

(*********************************************************************)

PROCEDURE ReadPerMax (j : Indexj);
   BEGIN
   ReadBool (PerMax [j]);   ReadLn;
   IF (NOT TroisChiffres [j]) AND (PerMax [j]) THEN  
      WriteLn;  WriteString (" **********************************");
      WriteLn;  WriteString (" WARNING: Since m is not given as 3 numbers,");
      WriteLn;  WriteString ("   PerMax [");  WriteInt (j, 2);
      WriteString ("] is reset to FALSE");  WriteLn;
      WriteString (" **********************************");  WriteLn;
      PerMax [j] := FALSE
      END;
   IF PerMax [j] THEN
      IF ((M2 [j] = 1) OR (M3 [j] # 0)) THEN
         IF IsPrime (mj [j], 100) THEN
            Primemj [j] := TRUE;
         ELSE
            WriteLn;  WriteString (" **********************************");
            WriteLn;  WriteString (" WARNING: Primemj [");  
            WriteInt (j, 2);  WriteString ("] is reset to FALSE"); 
            WriteLn;  WriteString (" because m_j is not prime.");
            WriteLn;  WriteString (" **********************************");
            Primemj [j] := FALSE;
            END
      ELSIF Orderj [j] > 1 THEN
         PerMax [j] := FALSE
         END
      END
   END ReadPerMax;

(*********************************************************************)

PROCEDURE ReadImplemCond (j : Indexj);
   VAR
      Done : BOOLEAN;
   BEGIN
   ReadLine (S);   ReadLn;   ItemS (Str1, S, Espace, 0);
   IF Match (Str1, 'AppFact') OR Match (Str1, 'TRUE') THEN
      ImplemCond [j] := AppFact
   ELSIF Match (Str1, 'MaxBits') THEN
      ImplemCond [j] := MaxBits;
      ItemS (Str1, S, Espace, 1);   
      NbMaxBits [j] := StrToInt (Str1, 10, Done);
      ItemS (Str1, S, Espace, 2);   
      HighestBit [j] := StrToInt (Str1, 10, Done);
      IF NOT Done THEN ErreurChamp (' ImplemCond with MaxBits ') END
   ELSE
      ImplemCond [j] := NoCond
      END;
   END ReadImplemCond;

(*********************************************************************)

PROCEDURE ReadFactmr (j : Indexj);
   (* Lecture de factorisation de m-1 et de r *)
   BEGIN
   EcriremMS1 [j] := FALSE;
   IF (Primemj [j]) THEN
      ReadLine (S);   ReadLn;   ItemS (Str1, S, Espace, 0);
      IF Match (Str1, 'Decomp') THEN
         DecomposeM [j] := Decomp;   FactmMS1 [j] := NIL
      ELSIF Match (Str1, 'DecompWrite') THEN
         DecomposeM [j] := DecompWrite;   FactmMS1 [j] := NIL;
         ItemS (FichmMS1 [j], S, Espace, 1);
         EcriremMS1 [j] := TRUE
      ELSIF Match (Str1, 'Read') THEN
         DecomposeM [j] := READ;   ItemS (FichmMS1 [j], S, Espace, 1);
         LireFact (FactmMS1 [j], FichmMS1 [j])
      ELSE
         ErreurChamp (' F1 ')
         END;
      ReadLine (S);   ReadLn;   ItemS (Str1, S, Espace, 0);
      Ecrirer [j] := FALSE;
      IF Match (Str1, 'Decomp') THEN
         DecomposeR [j] := Decomp;   Factr [j] := NIL
      ELSIF Match (Str1, 'DecompWrite') THEN
         DecomposeR [j] := DecompWrite;   Factr [j] := NIL;
         ItemS (Fichr [j], S, Espace, 1);   Ecrirer [j] := TRUE
      ELSIF Match (Str1, 'Read') THEN
         DecomposeR [j] := READ;   ItemS (Fichr [j], S, Espace, 1);
         LireFact (Factr [j], Fichr [j])
      ELSIF Match (Str1, 'Prime') THEN
         DecomposeR [j] := Prime;
         NEW (Factr [j]);
         WITH Factr [j]^ DO
            Create (Factor, 2);  Affect (mj [j], Factor);
            PowerSupInt (Factor, LONGCARD (Orderj [j]), Factor);
            Subtract (Factor, One, Factor);
            Subtract (mj [j], One, SupT);
            Quotient (Factor, SupT, Factor);
            Multiplicity := 1;   Prime := TRUE;   Next := NIL
            END
      ELSE
         ErreurChamp (' F2 ')
         END
   ELSE
      ReadLn;   ReadLn
      END;
   END ReadFactmr;

(*********************************************************************)

PROCEDURE Reada (j : Indexj);
   (* Lecture des aj [j,t].   *)
   VAR
     t: INTEGER;
   BEGIN
   FOR t := 1 TO Orderj [j] DO
      ReadOnea (aj [j,t]);
      IF NOT (Greater (aj [j,t], mmN) AND Greater (mm, aj [j,t])) THEN
         WriteString ("ILLEGAL VALUE for a_");  WriteInt (t, 1);
         WriteString (" : ");   WriteSup (aj [j,t], 10, 70);  WriteLn;
         WriteString ("mm  = ");   WriteSup (mm, 10, 70);  WriteLn;
         WriteString ("mmN = ");   WriteSup (mmN, 10, 70);  WriteLn;
         ErrorHalt ("  !");
         END;
      END;
   END Reada;

(*********************************************************************)

PROCEDURE Readbc (j : Indexj);
   (* Lecture des bornes bj [j,t] et cj [j,t].   *)
   VAR
     t: INTEGER;
   BEGIN
   FOR t := 1 TO Orderj [j] DO
      ReadOnea (bj [j,t]);
      (*  IF NOT OK THEN ErreurChamp (' b(j,t) ') END;  *)
      ReadOnea (cj [j,t]);
      (*  IF NOT OK THEN ErreurChamp (' c(j,t) ') END;  *)
      IF NOT (Greater (bj [j,t], mmN) AND (Greater (mm, cj [j,t])))
            AND (NOT Greater (bj [j,t], cj [j,t])) THEN
         ErrorHalt ("ILLEGAL VALUES for b[j,t] or c[i,t].")
         END
      END
   END Readbc;

(*********************************************************************)

PROCEDURE ReadSearchMethod (j : Indexj);
   (* Lecture de la methode de recherche et (si aleatoire) du nb. et de  *)
   (* la taille des regions.                                             *)
   VAR
      Done : BOOLEAN;
   BEGIN
   ReadLine (S);  ReadLn;  ItemS (Str1, S, Espace, 0);
   IF Match (Str1, 'Exhaust') OR Match (Str1, 'EXHAUST') THEN 
      Exhaust [j] := TRUE
   ELSIF Match (Str1, 'Random') OR Match (Str1, 'RANDOM') THEN 
      Exhaust [j] := FALSE
   ELSE ErreurChamp (' SearchMethod ') END;
   IF NOT Exhaust [j] THEN
      ItemS (Str1, S, Espace, 1);   NbReg [j] := StrToInt (Str1, 10, Done);
      IF NOT Done THEN ErreurChamp (' SearchMethod n ') END;
      ItemS (Str1, S, Espace, 2);   H [j] := StrToInt (Str1, 10, Done);
      IF NOT Done THEN ErreurChamp (' SearchMethod H ') END;
      ItemS (Str1, S, Espace, 3);   Hk [j] := StrToInt (Str1, 10, Done);
      IF NOT Done THEN ErreurChamp (' SearchMethod Hk ') END
   ELSE
      NbReg [j] := 1                 (* Rech. exhaustive.              *)
      END;
   END ReadSearchMethod;

(***********************************************************************)

PROCEDURE ReadMRGComponent (j : Indexj);
   (* Lit les parametres relies a une composante j du generateur.      *)
   VAR
     i: INTEGER;
   BEGIN
   ReadTypeGen (j);   Readm (j);   ReadOrder (j);   Primemj [j] := FALSE;
   IF Seek THEN
      ReadPerMax (j);  ReadImplemCond (j);  ReadFactmr (j);
      FOR i := 1 TO Orderj [j] DO
         Create (aj [j,i], 2);   MCreateScal (Maj [j, i]);
         Create (bj [j,i], 2);   Create (cj [j,i], 2);
         END;
      Readbc (j);
      ReadSearchMethod (j)
   ELSE
      FOR i := 1 TO Orderj [j] DO
         Create (aj [j,i], 2);   MCreateScal (Maj [j, i]);
         END;
      Reada (j)
      END;
   END ReadMRGComponent;

(*********************************************************************)

PROCEDURE ReadMinMaxDim;
   (* Lit la plage de dimensions a parcourir.                        *)
   VAR
      C : LONGINT;
   BEGIN
   MaxAllCat := TRUE;
   IF Seek THEN ReadInt (NbCat) ELSE  NbCat := 1 END;
   IF (NbCat < 1) THEN
      ErreurChamp (' ReadMinMaxDim: NbCat < 1')
      END;
   ReadInt (MinDim);   TabDim [0] := MinDim - 1;
   FOR C := 1 TO NbCat DO
      ReadInt (TabDim [C]);
      IF TabDim [C] < 0 THEN
         (* Dans cette categorie, on minimise la fig. de merite.     *)
         TabDim [C] := -TabDim [C];
         MaximCat [C] := FALSE;   MaxAllCat := FALSE
      ELSE
         MaximCat [C] := TRUE
         END;
      IF (TabDim [C] <= TabDim [C-1]) THEN
         ErreurChamp (' ReadMinMaxDim: Valeurs pas en ordre croissant');
         END;
      END;
   MaxDim := TabDim [NbCat];
   ReadLn;
   IF ( (MinDim < 2) OR (MaxDim > BMaxDim) )
         OR (MinDim > TabDim [1]) THEN
      ErreurChamp (' ReadMinMaxDim: illegal MinDim or MaxDim')
      END;
   END ReadMinMaxDim;

(*********************************************************************)

PROCEDURE ReadMinMaxMerit;
   (* Lit les seuil min. et max. d'acceptabilite pour le critere,    *)
   (* pour chaque categorie.                                         *)
   VAR
      C    : LONGINT;
   BEGIN
   FOR C := 1 TO NbCat DO
      ReadLR (MinMerit [C]);  ReadLR (MaxMerit [C]);
      IF (MinMerit [C] < 0.0) OR (MaxMerit [C] > 1.0) 
            OR (MinMerit [C] > MaxMerit [C]) THEN 
         ErreurChamp (' MinMaxMerit') 
         END;
      END;
   ReadLn;
   END ReadMinMaxMerit;

(*********************************************************************)

PROCEDURE ReadNbGen;
   (* Lit le nombre de generateurs a retenir dans chaque categorie.  *)
   VAR
      C : LONGINT;
   BEGIN
   FOR C := 1 TO NbCat DO  
      ReadInt (NbGen [C]);
      IF ((NbGen [C] < 0) OR (NbGen [C] >= MaxNbGen)) THEN
         ErreurChamp (' NbGen ')
         END
      END;
   ReadLn;
   END ReadNbGen;

(*********************************************************************)

PROCEDURE ReadCriterion;
   (* Lit le critere de selection.                                   *)
   VAR 
      i : INTEGER;
   BEGIN
   UsedNorm := L2Norm; 
   ReadLine (S);  ReadLn;  ItemS (Str1, S, Espace, 0);
   IF Match (Str1, 'Invert') THEN 
      InvertCrit := TRUE;    i := 2;
      (*  WriteString (Str1);  WriteLn;  *)
      ItemS (Str1, S, Espace, 1); 
   ELSE
      InvertCrit := FALSE;   i := 1;
      END;
   IF    Match (Str1, 'Beyer')    THEN 
      Criterion := Beyer
   ELSIF (Match (Str1, 'Spectral') OR Match (Str1, 'SpectralP')) THEN
      Criterion := Spectral;
      DualLattice := Match (Str1, 'Spectral');
      ItemS (Str2, S, Espace, i);
      IF Match (Str2, 'BestLat') THEN 
         Critere2 := BestLat;
      ELSIF Match (Str2, 'Minkowski') THEN 
         Critere2 := Minkowski;
      ELSIF Match (Str2, 'Laminated') THEN 
         Critere2 := Laminated;
      ELSIF Match (Str2, 'Rogers') THEN 
         Critere2 := Rogers;
      ELSE  ErreurChamp (' Criterion, data field 2')
         END
   ELSIF Match (Str1, 'SpectralL1') THEN
      Criterion := SpectralL1;   Critere2 := MinkL1;
      UsedNorm := L1Norm;
   ELSE   ErreurChamp (' Criterion, data field 1') 
      END;
   END ReadCriterion;

(*********************************************************************)

PROCEDURE ReadLatInfo;
   (* Lit le choix d'information a calculer en chaque dimension.     *)
   BEGIN
   ReadLine (S);   ReadLn;   ItemS (Str1, S, Espace, 0);
   IF    Match (Str1, 'Beyer')         THEN 
      LatInfo := Beyer
   ELSIF Match (Str1, 'Spectral') THEN
      LatInfo := Spectral
   ELSIF Match (Str1, 'SpectralP') THEN
      LatInfo := Spectral;   DualLattice := FALSE
   ELSIF Match (Str1, 'BeyerSpectral') THEN
      LatInfo := BeyerSpectral
   ELSIF Match (Str1, 'SpectralL1') THEN
      LatInfo := SpectralL1;   Critere2 := MinkL1;
      UsedNorm := L1Norm;
   ELSE ErreurChamp (' LatInfo, data field 1 ') 
      END;
   IF (NOT Seek) AND (LatInfo # Beyer) AND (LatInfo # SpectralL1) THEN
      ItemS (Str2, S, Espace, 1);
      IF Match (Str2, 'BestLat') THEN 
         Critere2 := BestLat;
      ELSIF Match (Str2, 'Minkowski') THEN 
         Critere2 := Minkowski;
      ELSIF Match (Str2, 'Laminated') THEN 
         Critere2 := Laminated;
      ELSIF Match (Str2, 'Rogers') THEN 
         Critere2 := Rogers;
      ELSE  ErreurChamp (' LatInfo, data field 2')
         END;
      END;
   END ReadLatInfo;

(*********************************************************************)
PROCEDURE ReadLatType;
   (* Lit quel type de reseau on veut analyser.                      *)
   (* Calcule ensuite...                                             *)
   VAR
      i, i1 : MDim;
      j: INTEGER;
   BEGIN
   ReadString (Str1);
   IF    Match (Str1, 'Full')         THEN LatType := Full; ReadLn;
   ELSIF Match (Str1, 'Recurrent')    THEN LatType := Recurrent; ReadLn;
   ELSIF Match (Str1, 'Orbit')    THEN
      LatType := Orbit;
      FOR  j := 1  TO  J DO
	 FOR  i := 1  TO  VAL (MDim, Order)  DO
	    IF  j = 1  THEN  IntToSup (0, InSta[i])  END;
	    IF  i <= VAL (MDim, Orderj[j])  THEN
	       ReadSup (VectSup [i], 10)
	    ELSE
	       IntToSup (0, VectSup [i]);
	       FOR  i1 := 1  TO  VAL (MDim, Orderj [j])  DO
		  Multiply (aj [j,i1], VectSup [i-i1], SupT3);
		  Add (SupT3, VectSup [i], VectSup [i])
		  END
	       END;
	    Multiply (nj [j], VectSup [i], SupT3);
	    Add (InSta [i], SupT3, InSta [i]);
	    IF  j = J  THEN  Modulo (InSta [i], mm, InSta [i])  END
	    END;
	 ReadLn
	 END;
   ELSIF Match (Str1, 'PrimePower')  THEN
      LatType := PrimePower;  ReadLn;
      FOR j := 1 TO J DO
         IF NOT TroisChiffres [j] THEN
            ErreurChamp (' When PrimePower, m_j must be expressed by 3 numbers')
            END;
         IF M3 [j] # 0 THEN
            ErreurChamp (' When PrimePower, m_j must be a power of a prime')
            END;
         IF Orderj [j] > 1 THEN
            ErreurChamp (' When PrimePower, order k_j must be 1')
            END
         END
   ELSE  ErreurChamp (' LatticeType ') END;
   END ReadLatType;

(************************************************************************)

PROCEDURE ReadLaIndices;
   (* Lit les indices (lacunaires ou successifs) que l'on veut traiter. *)
   VAR
      La1, s1, t : INTEGER;
   BEGIN
   ReadInt (La1);
   IF  (La1 > 0)  THEN  ReadSup (SupT1, 10)  END;   ReadLn;
   IF ((La1 = 1) AND (Equal (SupT1, One))) OR (La1 > MaxDim) THEN
      Lacunary := FALSE;
      IF MaxDim <= Order THEN  
         ErrorHalt ('From ReadLaIndices: MaxDim not larger the Order')
         END;
      IF MinDim <= Order THEN MinDim := Order + 1 END;
      RETURN
   ELSE
      Lacunary := TRUE
      END;
   IF La1 < 0 THEN
      (* Lacunary indices are written explicitly in file.  *)
      FOR t := 1 TO MaxDim DO  BReadScal (LacI [t]);  ReadLn  END;
      RETURN
      END;
   (* Otherwise, the lacunary (or not) indices are evenly spaced.        *)
   t := 1;   IntToSup (0, SupT);
   WHILE TRUE DO
      FOR s1 := 0 TO (La1-1) DO
         IF t <= MaxDim THEN
            IntToSup (IToLI (s1), h);  Add (SupT, h, h);
            SupToBScal (h, LacI [t]);  INC (t)
         ELSE
            RETURN
            END
         END;
      Add (SupT, SupT1, SupT);
      END;
   END ReadLaIndices;

(*********************************************************************)

PROCEDURE ReadVerifyBB;
   (* Lit le niveau de verification requis.                          *)
   BEGIN
   ReadLine (S);   ReadLn;   ItemS (Str1, S, Espace, 0);
   IF    Match (Str1, 'VerifyAll2')      THEN 
      Verif := VerifyAll2;      VerifyAll := Verify2;  VerifyRet := Verify2
   ELSIF Match (Str1, 'VerifyRetained2') THEN 
      Verif := VerifyRetained2; VerifyAll := Verify0;  VerifyRet := Verify2
   ELSIF Match (Str1, 'VerifyAll3')      THEN
      Verif := VerifyAll3;      VerifyAll := Verify3;  VerifyRet := Verify3
   ELSIF Match (Str1, 'VerifyRetained3') THEN
      Verif := VerifyRetained3; VerifyAll := Verify0;  VerifyRet := Verify3
   ELSIF Match (Str1, 'NoVerify')        THEN 
      Verif := NoVerify;        VerifyAll := Verify0;  VerifyRet := Verify0
   ELSE ErreurChamp (' VerifyBB ') END;
   END ReadVerifyBB;

(*********************************************************************)

PROCEDURE ReadMaxNodesBB;
   (* Lit le nb. max de noeuds dans le branch-and-bound.             *)
   (* Lorsque le nb. de noeuds depasse ce nb., on arrete.            *)
   BEGIN
   ReadLongInt (MaxNodesBB);   ReadLn;
   IF MaxNodesBB < 1 THEN ErreurChamp (' MaxNodesBB ') END;
   END ReadMaxNodesBB;

(*********************************************************************)

PROCEDURE ReadTimeLimit;
   (* Temps limite de cpu.                                           *)
   BEGIN
   ReadLR (TempsLimite);   ReadLn;
   IF TempsLimite <= 0.0 THEN ErreurChamp (' TimeLimit '); END;
   END ReadTimeLimit;

(*********************************************************************)

PROCEDURE ReadSeeds;
   (* Valeurs initiales du gener. de v.a. (pour recherche aleatoire) *)
   VAR
      succes : BOOLEAN;
   BEGIN
   ReadLine (S);   ReadLn;
   ItemS (Str1, S, Espace, 0);   Seed1 := StrToInt (Str1, 10, succes);
   IF NOT succes THEN ErreurChamp (' Seed Str1 ') END;
   ItemS (Str1, S, Espace, 1);   Seed2 := StrToInt (Str1, 10, succes);
   IF NOT succes THEN ErreurChamp (' Seed S2 ') END;
   SetSeed (Seed1, Seed2);
   END ReadSeeds;

(*********************************************************************)

PROCEDURE ReadResultForm;
   (* Lit la forme du ou des fichier(s) de resultats.                *)
   BEGIN
   ReadLine (S);   ReadLn;   ItemS (Str1, S, Espace, 0);
   IF Match (Str1, 'Terminal') OR Match (Str1, 'terminal') 
         OR Match (Str1, 'TER') THEN
      IF Seek THEN ResultForm := STerminal ELSE ResultForm := LTerminal END;
   ELSIF Match (Str1, 'RES') OR Match (Str1, 'res') THEN
      ResultForm := RES;
   ELSIF Match (Str1, 'GEN') OR Match (Str1, 'gen') THEN
      ResultForm := GEN;
      IF NOT Seek THEN ErreurChamp (' ResultForm for lat program.') END
   ELSIF Match (Str1, 'RESGEN') OR Match (Str1, 'resgen') THEN
      ResultForm := RESGEN;
      IF NOT Seek THEN ErreurChamp (' ResultForm for lat program.') END;
   ELSIF Seek THEN ErreurChamp (' ResultForm for Seek.')
   ELSIF Match (Str1, 'TEX') OR Match (Str1, 'tex') THEN 
      ResultForm := TEX
   ELSE ErreurChamp (' ResultForm.') END;
   END ReadResultForm;

(****************************************************************************)

PROCEDURE Computem;
   (* Computes Order and m for combined generators.                   *)
   (* Calcule aussi Rho et les Rhoj[j].                               *)
   VAR
      j : INTEGER;
   BEGIN
   Affect (One, mm);   Order := 1;
   IntToSup (1, LossRho);   IntToSup (1, Rho);
   FOR j := 1 TO J DO
      Multiply (mm, mj [j], mm);
      IF Orderj [j] > Order THEN Order := Orderj [j] END;
      IF Seek AND Primemj [j] THEN SupToMScal (mj [j], Mmj [j]) END
      END;
   FOR  j := 1  TO  J  DO
      (* Calcul de nj [j].   *)
      Quotient (mm, mj [j], mSurmj [j]);
      Euclide (mSurmj [j], mj [j], nj [j], SupT, SupT1, SupT2, SupT3);
      IF Negative (SupT3) THEN  ChangeSign (nj [j], nj [j])  END;
      Multiply (mSurmj [j], nj [j], nj [j]);

      (* Calcul de Rhoj [j], Rho, et LossRho.  *)
      PowerSupInt (mj [j], Orderj [j], SupT3);
      Subtract (SupT3, One, Rhoj [j]);
      GCD (Rho, Rhoj [j], SupT3);
      Multiply (LossRho, SupT3, LossRho);
      Multiply (Rho, Rhoj [j], Rho);
      Quotient (Rho, SupT3, Rho);
      END
   END Computem;

(*********************************************************************)

PROCEDURE Computea;
   (* Computes a for combined generators (assuming prime moduli).    *)
   (* Initializes Maj  and a.                                        *)
   VAR
      i, j : INTEGER;
   BEGIN
   IF J = 1 THEN
      FOR i := 1 TO Order DO
         SupToMScal (aj [1,i], a [i]);   MAffect (a [i], Maj [1,i])
         END
   ELSE
      FOR j := 1 TO J DO
         (* Calcul de nj [j].       Note: fait aussi dans Computem.    *)
         Quotient (mm, mj [j], mSurmj [j]);
         Euclide (mSurmj [j], mj [j], nj [j], SupT, SupT1, SupT2, SupT3);
         IF Negative (SupT3) THEN  ChangeSign (nj [j], nj [j])  END;
         Multiply (mSurmj [j], nj [j], nj [j]);
         END;
      FOR  i := 1  TO  Order  DO
         IntToSup (0, Sa [i]);
         FOR  j := 1  TO  J  DO
            IF  Orderj [j] >= i  THEN
               SupToMScal (aj [j,i], Maj [j,i]);
               Multiply (aj [j,i], nj [j], SupT3);
               Add (SupT3, Sa [i], Sa [i]);
               END
            END;
         Modulo (Sa [i], mm, Sa [i]);  SupToMScal (Sa [i], a [i])
         END;
      FOR  j := 1  TO  J  DO
         Subtract (Sa [1], aj [j,1], SupT3);
         Modulo (SupT3, mj [j], SupT3);
         IF  NOT Equal (SupT3, Zero)  THEN
            WriteSup (aj [j,1], 10, 60);  WriteLn;
            ErrorHalt (' ERREUR RECURRENCE dans Computea');
            END
         END
      END
   END Computea;

(************************************************************************)

PROCEDURE SaisieDonnees;
   (* Reads data from the data file.                                    *)
   VAR
      z : INTEGER;
      i, j: INTEGER;
   BEGIN
   ReadReadGen;   ReadInt (J);  ReadLn;
   FOR j := 1 TO J DO
      Create (mj [j], 4);     Create (mjm2 [j], 4);    Create (mjRed [j], 4);
      Create (nj [j], 4);     Create (mSurmj [j], 4);  Create (Rhoj [j], 4);
      Create (mRac [j], 4);   Create (mRacNeg [j], 4);
      MCreateScal (Mmj [j]);
      IF Seek THEN
         FOR z := 1 TO MaxZones DO  Create (Frontiere [j, z], 2)  END;
         END;
      ReadMRGComponent (j);
      END;
   Computem;
   MCreateVect (a, 0, Order);
   FOR i := 1 TO Order DO Create (Sa [i], 4)  END;
   ReadMinMaxDim;
   BCreateVect (LacI, 0, MaxDim);
   IF Seek THEN  ReadMinMaxMerit;  ReadNbGen;  ReadCriterion  END;
   ReadLatInfo;
   ReadLatType;  
   ReadLaIndices;
   (* IF (NOT Streams) THEN ReadLaIndices  ELSE ReadLn;  END;  *)
   ReadVerifyBB;  ReadMaxNodesBB;
   IF Seek THEN   ReadTimeLimit;   ReadSeeds  END;
   ReadResultForm;
   END SaisieDonnees;

(********************************************************************)

PROCEDURE ReadGenFile;
   (* Reads a set of generators from a .gen file.                   *)
   VAR
      out0 : FILE;   J1, k1 : INTEGER;
      j: INTEGER;
   BEGIN
   GetOutput (out0);  SetOutput (stdOut);
   Concat (S, FichGen, '.gen');   OpenAsInput (S);  (*  GetInput (FIn); *)
   ReadInt (J1);   ReadLn;
   IF J1 # J THEN ErrorHalt ("J in .dat and .gen files do not agree.") END;
   FOR j := 1 TO J DO
      ReadSup (SupT3, 10);   ReadLn;   ReadInt (k1);  ReadLn;
      IF NOT Equal (SupT3, mj [j]) THEN
         ErrorHalt ("Files .dat and .gen do not agree on moduli.")
         END;
      IF (k1 # Orderj [j]) THEN
         ErrorHalt ("Files .dat and .gen do not agree on orders.")
         END
      END;
   ReadInt (NbGenFile);   ReadLn;
   SetOutput (out0);
   END ReadGenFile;

(****************************************************************************)

PROCEDURE PerMaxPowPrime (j : Indexj) : BOOLEAN;
   (* Assumes that m_j is a power of a prime p, k_j = 1, and the recurrence *)
   (* is homogeneous.   Returns TRUE iff the maximal period conditions are  *)
   (* satisfied for that case for component j.                              *)
   BEGIN
   IF M1[j] = 2 THEN
      MModulo (Maj[j,1], MEight, MTemp);
      RETURN (MEqual (MTemp, MFive) OR MEqual (MTemp, MThree))
   ELSE
      MScalToSup (Maj[j,1], aj[j,1]);    IntToSup (M1[j], P);
      Multiply (P, P, P2);   Subtract (P, One, Pm1);    (* Pm1 =  M1[j]-1 *)
      PowerMod (aj[j,1], Pm1, P2, SupT);
      RETURN NOT Equal (SupT, One)
      END
   END PerMaxPowPrime;

(****************************************************************************)

PROCEDURE Reducemj (VAR a : MVect);
   (* Appel\'e de TestGen dans le cas  LatType = PrimePower.                *)
   (* Reduit m_j et initialise le module MRG.                               *)
   VAR
      j, R : INTEGER;
   BEGIN
   IntToSup (1, mm);
   FOR j := 1 TO J DO
      IF TroisChiffres [j] AND (M3 [j] = 0) THEN
         (* We now assume that mj is a power of a prime p = M1[j].          *)
         IF M1 [j] = 2 THEN
            (* mj is a power of two.  *)
            MModulo (Maj[j,1], MEight, MTemp);
            IF MEqual (MTemp, MFive) THEN
               Quotient (mj [j], Four, mjRed [j])
            ELSIF MEqual (MTemp, MThree) THEN
               Quotient (mj [j], Eight, mjRed [j])
            ELSE
               MAffect (Maj[j,1], MTemp2);   MAffect (MEight, MTemp3);
               IF MEqual (MTemp, MOne) THEN  MInc (MTemp2, -1)
               ELSIF MEqual (MTemp, MSeven) THEN  MInc (MTemp2, 1)
               ELSE  ErrorHalt ("Power of 2 modulus with even multiplier")
                  END;
               REPEAT
                  MAdd (MTemp3, MTemp3, MTemp3);
                  MModulo (MTemp2, MTemp3, MTemp4)
               UNTIL (NOT MEqual (MTemp4, MZero));
               MScalToSup (MTemp3, P2);
               Quotient (mj [j], P2, mjRed [j])
               END
         ELSE
            (* mj is a power of a prime p > 2.   *)
            IF PerMaxPowPrime (j) THEN
               DivideSupInt (mj [j], M1[j], mjRed [j], R)
            ELSE
               REPEAT
                  MultiplyIntSup (M1[j], P2, P2);        (* P2 = p^e *)
                  PowerMod (aj[j,1], Pm1, P2, SupT);
               UNTIL (NOT Equal (SupT, One));
               DivideSupInt (P2, M1[j], P2, R);
               Quotient (mj [j], P2, mjRed [j])
               END
            END
         END;
      Multiply (mm, mjRed [j], mm)
      END;
   SupToMScal (mm, mRed); 
   InitMRG (mRed, 1, MaxDim);
   END Reducemj;

(****************************************************************************)

PROCEDURE CalculBorneInf (VAR b, c, Borne : SuperInteger; NoZone, j : INTEGER);
   (* Calcule la borne inferieure de l'intersection d'une zone avec [b..c]. *)
   (* Si NoZone = 1 ou 3, la borne retournee sera (approx) q t.q. [m/q] = c.*)
   (* Si NoZone = 2, retourne b.                                            *)
   (* A l'appel, b est toujours >= borne inf. de la zone.                   *)
   BEGIN
   (* note : mRac [j] = trunc (sqrt (mj [j])) *)
   CASE NoZone OF
      1 : (* b <= -sqrt(m)-1 *)
          IF Smaller (c, mRacNeg [j]) THEN
             Subtract (mj [j], One, SupT);   Add (c, One, SupT1);
             Divide (SupT, SupT1, Borne, SupT);
             IF NOT Equal (SupT, Zero) THEN Add (Borne, One, Borne) END;
             IF Smaller (Borne, mRacNeg [j]) THEN
                Affect (mRacNeg [j], Borne)
                END
          ELSE
             Affect (mRacNeg [j], Borne);
             END; |
      2 : (* -sqrt(m)-1 < b <= sqrt(m);   *)
          Affect (b, Borne); |
      3 : (* b > sqrt(m) *)
          (* On retourne le a minimal tel que b <= floor(m/a) <= c.       *)
          (* Note: floor(m/Borne) <= c, m/Borne < c+1, Borne > m/(c+1).   *)
          (* On fait: Borne := (m DIV (c+1)) + 1.                         *)
          Add (c, One, SupT1);    Quotient (mj [j], SupT1, SupT);
          Add (SupT, One, SupT);  Affect (SupT, Borne)
      END;
   END CalculBorneInf;

(****************************************************************************)

PROCEDURE CalculBorneSup (VAR b, c, Borne : SuperInteger; NoZone, j : INTEGER);
   (* Calcule la borne superieure de l'intersection d'une zone avec [b..c]. *)
   (* Si NoZone = 1 ou 3, la borne retournee sera (approx) q t.q. m/q = b.  *)
   (* Si NoZone = 2, retourne  min (c, sqrt{m}).                            *)
   BEGIN
   CASE NoZone OF
      1 : (* b <= -sqrt(m)-1 *)
          Quotient (mj [j], b, Borne) |
      2 : (* -sqrt(m)-1 < b <= sqrt(m) *)
          IF Smaller (mRac [j], c) THEN  Affect (mRac [j], Borne)
          ELSE Affect (c, Borne) END; |
      3 : (* b > sqrt(m) *)
          (* On retourne le a maximal tel que b <= floor(m/a) <= c. *)
          Quotient (mj [j], b, Borne);
          IF Smaller (mRac [j], Borne) THEN Affect (mRac [j], Borne) END
      END;
   END CalculBorneSup;

(****************************************************************************)

PROCEDURE InitZones (j, i : INTEGER);
   (* Initialise les zones de recherche pour le multiplicateur aj[j,i].     *)
   (* Appele par SetupGenSeek.                                              *)
   (* Dans le cas de recherche aleatoire, cree aussi la region [i,j].       *)
   VAR
      k            : INTEGER;      (* Zone number.                          *)
      LRE, TotLR   : LONGREAL;
      Z, pZ        : ToZone;
      FirstZone    : BOOLEAN;
   BEGIN
   IF ((ImplemCond [j] = AppFact) AND (i = 1)) THEN
      (* Calcul des frontieres superieures des 3 zones.                     *)
      ChangeSign (mRac [j], Frontiere [j,1]);
      Subtract (Frontiere [j,1], One, Frontiere [j,1]); (* = -sqrt{m_j}-1   *)
      Affect (mRac [j], Frontiere [j,2]);               (* = sqrt{m_j}      *)
      Subtract (mj [j], One, Frontiere [j,3]);          (* = m_j-1          *)
      DivQ [1] := TRUE;   DivQ [2] := FALSE;   DivQ [3] := TRUE;
      (* Si DivQ [i] = TRUE, on cherche les a=m/q avec q entre les bornes.  *)
      END;

   (* Calcul des bornes pour aj[j,i] ou pour q (zone 1 ou 3) dans ch. zone. *)
   IF NOT Exhaust [j] THEN
      IF i = Orderj [j] THEN IntToSup (Hk [j], h)
      ELSE IntToSup (H [j], h)  END       (* Taille des regions pour [j,i]. *)
      END;
   Affect (bj [j,i], Eb);   Affect (cj [j,i], Ec);
   IF (ImplemCond [j] # AppFact) THEN
      (* Pas de contrainte d'implantation;  une seule grande zone.         *)
      CreateZone (bcZone [j,i]);
      WITH bcZone [j,i]^ DO
         Affect (Eb, Binf);   Affect (Ec, Bsup); (* Les bornes de la zone. *)
         IF NOT Exhaust [j] THEN
            (* Ajuster taille des regions qui seront tirees au hasard.     *)
            p := 1.0;   Subtract (Bsup, Binf, E);
            PetiteDiff := Smaller (E, h);
            IF NOT PetiteDiff THEN
               Add (Bsup, One, BsupMsH);  Subtract (BsupMsH, h, BsupMsH)
               END;
            END;
         NextZone := NIL;
         END;
   ELSE   (* La contrainte AppFact est appliquee.  Max. de 3 zones.       *)
      IntToSup (0, Tot);   FirstZone := TRUE;   k := 1;
      (* Trouver la premiere zone k s'intersectant avec [Eb, Ec].         *)
      WHILE (k < MaxZones) AND Smaller (Frontiere [j,k], Eb) DO INC (k) END;

      (* Initialisation de la zone k. *)
      WHILE NOT Greater (Eb, Ec) DO
         CreateZone (Z);
         IF FirstZone THEN
            bcZone [j,i] := Z;   FirstZone := FALSE
         ELSE
            pZ^.NextZone := Z;            (* pZ est la zone precedant Z.    *)
            IF NOT Exhaust [j] THEN ApproxTotGen [j] := TRUE END
            END;
         pZ := Z;
         WITH Z^ DO
            No := k;
            CalculBorneInf (Eb, Ec, Binf, k, j);  (* Bornes de la zone.     *)
            CalculBorneSup (Eb, Ec, Bsup, k, j);
            Subtract (Bsup, Binf, E);             (* Taille de la zone, -1. *)
            Add (Tot, E, Tot);   Add (Tot, One, Tot);
            IF NOT Exhaust [j] THEN
               (* Ajuster taille des regions qui seront tirees au hasard.   *)
               PetiteDiff := Smaller (E , h);
               IF PetiteDiff THEN
                  WriteString ('** WARNING ** Multiplier');
                  WriteInt (i, 2);  WriteString (' zone');  WriteInt (k, 2);
                  WriteString (' : Bsup - Binf + 1 < H(k). ');  WriteLn
               ELSE
                  Add (Bsup, One, BsupMsH);  Subtract (BsupMsH, h, BsupMsH)
                  END
               END
            END;
         Add (Frontiere [j, k], One, Eb);   (* passer a la zone suivante.  *)
         INC (k);
         END;   (* du WHILE *)
      Z^.NextZone := NIL;

      (* Calculer la proportion p que represente chaque zone.              *)
      Z := bcZone [j,i];
      WHILE Z # NIL DO
         Subtract (Z^.Bsup, Z^.Binf, E);   Add (E, One, E);
         SupToLongReal (E, LRE);   SupToLongReal (Tot, TotLR);
         Z^.p := LRE / TotLR;      Z := Z^.NextZone;
         END;
      END;
   IF NOT Exhaust [j] THEN CreateRegion (Reg [j,i]) END;
   END InitZones;

(****************************************************************************)

PROCEDURE ChoisirBornes (j : Indexj);
   (* Choisir une region au hasard et en initialiser les bornes.            *)
   (* On fouillera ensuite completement cette region.                       *)
   (* Utilise avec la methode de recherche RANDOM seulement.                *)
   (* Cette procedure modifie  Reg [j,1], ..., Reg [j, Orderj [j]].         *)
   (* Appele par SeekGen.                                                   *)
   VAR
      i : INTEGER;  Z : ToZone;   h : LONGINT;   p, u : LONGREAL;
   BEGIN
   INC (CptRegions [j]);
   FOR i := 1 TO Orderj [j] DO
      Z := bcZone [j, i];
      IF Z^.NextZone # NIL THEN
         (* Choisir d'abord l'une des zones selon les probabilites Z^.p    *)
<* IF XDSV = "99" THEN *>
         u := RandU01 (RngBornes);
<* ELSE *>
         u := Uniform01 (2);
   <* END *>
         p := Z^.p;
         WHILE (u > p) AND (Z # NIL) DO Z := Z^.NextZone; p := p + Z^.p END
         END;
      (* Z pointe a la zone choisie.                                       *)
      IF Z^.PetiteDiff THEN
         (* On prends toute la zone.                                       *)
         SupToMScal (Z^.Binf, Reg [j,i]^.Binf);
         SupToMScal (Z^.Bsup, Reg [j,i]^.Bsup);
      ELSE
         (* On prends un intervalle de taille h, au hasard, dans la zone.  *)
         IF i = Orderj [j] THEN h := Hk[j] -1 ELSE h := H[j] - 1 END;
         SupRandom (Z^.Binf, Z^.BsupMsH, SupT);
         SupToMScal (SupT, Reg[j,i]^.Binf);
         SupToMScal (SupT, Reg[j,i]^.Bsup);
         MInc (Reg [j,i]^.Bsup, h)
         END;
      Reg [j,i]^.No := Z^.No;
      END
   END ChoisirBornes;

(****************************************************************************)

PROCEDURE TestGen
   ( VAR a    : MVect;
     T        : CriterionType;
     VerifyBB : VerifyType;
     Out      : OutputType
   );
   (* Teste le generateur combine de multiplicateur a et modulo m.         *)
   BEGIN
   IF LatType = PrimePower THEN  Reducemj (a) END;
   IF Lacunary THEN
      TestLa (a, LacI, T, MinDim, MaxDim, VerifyBB, Out)
   ELSE
      Test (a, T, MinDim, MaxDim, VerifyBB, Out)
      END
   END TestGen;

(****************************************************************************)

PROCEDURE ConserverGen (C : LONGINT;  tMerit2 : BDim);
   (* Mettre le generateur courant (competitif) dans la liste a conserver.  *)
   VAR
      G, GSuiv : Generateur;
      i, j     : INTEGER;
      Merit2   : LONGREAL;
   BEGIN
   IF NbGen [C] < 1 THEN RETURN END;  (* Ne conserve rien dans cette cat. *)
   IF Caff [C] < NbGen [C] THEN  INC (Caff [C])  END;
   G := PireGen [C];
   (* Copier les resultats dans le generateur *)
   CASE Criterion OF
      Beyer :
              Merit2 := Q2 [tMerit2];
                 IF ResultForm # GEN THEN 
                    FOR i := Order+1 TO TabDim [C] DO
                       G^.Res^.RQ2[i] := Q2[i];
                       END;
                    END;
                 G^.Merit := Merit2; |
      Spectral, SpectralL1 : 
              Merit2 := S2 [tMerit2];
                 IF ResultForm # GEN THEN
                    FOR i := Order+1 TO TabDim [C] DO
                       IF (i <= CAST (INTEGER, NormalG^.Maxt)) THEN 
                           G^.Res^.RS2 [i] := S2 [i] 
                           END;
                       G^.Res^.RD2 [i] := D2 [i];
                       END;
                    END;
                 G^.Merit := Merit2;
      END;
   IF NbGen [C] > 1 THEN
      (* Place dans la liste ordonnee, sinon ne conservera que ce          *)
      (* nouveau generateur (si NbGen [C] = 1).                            *)
      GSuiv := G^.NextGen;
      WHILE (GSuiv # NIL) AND ( (GSuiv^.DimMerit = 0) 
            OR ((Merit2 > GSuiv^.Merit) AND (MaximCat [C])) 
            OR ((Merit2 < GSuiv^.Merit) AND (NOT MaximCat [C])) ) DO
         G := GSuiv;   GSuiv := G^.NextGen
         END;
      G^.NextGen := PireGen [C];  G := PireGen [C];
      PireGen [C] := G^.NextGen;  G^.NextGen := GSuiv
      END;
   G^.DimMerit := tMerit2;
   (* Copie les multiplicateurs du generateur combine et des composantes.  *)
   IF J > 1 THEN 
      MCopyVect (a, G^.a, Order)
   ELSE 
      MCopyVect (Maj[1], G^.a, Order)  
      END;
   FOR j := 1 TO J DO  MCopyVect (Maj[j], G^.Maj[j], Orderj [j]) END;

   (* Ajuste Minq2 [NbCat], Mins2 [NbCat], etc., si approprie.             *)
   IF C = NbCat THEN
      WITH PireGen [C]^ DO
         IF DimMerit = 0 THEN  RETURN  END;
         CASE Criterion OF
            Beyer    : 
               IF (MaximCat [C]) AND (Merit > Minq2 [MaxDim]) THEN 
                  FOR i := (1 + TabDim [C-1]) TO MaxDim DO
                     Minq2 [i] := Merit 
                     END
               ELSIF (NOT MaximCat [C]) AND (Merit < Maxq2 [C]) THEN
                  FOR i := (1 + TabDim [C-1]) TO MaxDim DO
                     Maxq2 [i] := Merit 
                     END
                  END;
          | Spectral, SpectralL1 : 
               IF (MaximCat [C]) AND (Merit > Mins2 [MaxDim]) THEN 
                  FOR i := (1 + TabDim [C-1]) TO MaxDim DO
                     Mins2 [i] := Merit 
                     END
               ELSIF (NOT MaximCat [C]) AND (Merit < Maxs2 [C]) THEN
                  FOR i := (1 + TabDim [C-1]) TO MaxDim DO
                     Maxs2 [i] := Merit 
                     END
                  END;
            END
         END
      END
   END ConserverGen;

(****************************************************************************)

PROCEDURE VerifyCategories (VAR Me2 : BASISLR.BVect);
   (* Called by InsideExam.  Me2 is either Q2 or S2.        *)
   VAR  
      C, Ind, IndMin, MaxI : INTEGER;
   BEGIN
   Ind := Order + 1;   IndMin := Ind;
   FOR C := 1 TO NbCat DO
      INC (NbTried [C]);
      IF (C < NbCat) OR ((C = NbCat) AND TestCompleted) THEN
         (* On trouve ou le min est atteint pour cette categorie.   *)
         IF ((Criterion = Spectral) OR (Criterion = SpectralL1))
               AND (TabDim [C] <= CAST (INTEGER, NormalG^.Maxt)) THEN
            MaxI := TabDim [C]
         ELSE
            MaxI := NormalG^.Maxt
            END;
         WHILE Ind <= MaxI DO
            IF Me2[Ind] <= 0.0 THEN  RETURN  END;
            IF (Me2[Ind] < Me2[IndMin]) THEN  IndMin := Ind  END;
            INC (Ind);
            END;
         IF (Me2[IndMin] > MaxMerit [C] * MaxMerit [C]) THEN RETURN END;
         WITH PireGen [C]^ DO
            IF (DimMerit = 0)
                  OR ((MaximCat [C]) AND (Me2 [IndMin] >= Merit))
                  OR ((NOT MaximCat [C]) AND (Me2 [IndMin] <= Merit)) THEN
               ConserverGen (C, IndMin);
               END
            END;
         END;
      END;
   END VerifyCategories;

(****************************************************************************)

PROCEDURE ExamThisaj (j, i : INTEGER;  Pow2 : BOOLEAN;  Exam : ProcII);
   (* Called by InsideExam.  Examines the current a_j.                    *)
   VAR
      Ok : BOOLEAN;
      P  : Poly;
   BEGIN
      Ok := TRUE;
      IF (NOT Pow2) AND PerMax [j] AND (i = Orderj [j]) THEN
         (* On verifie cond.(a) pour periode max.                         *)
         IF Primemj [j] THEN       (* m_j is a prime.                     *)
            IF PrimElem (Maj [j]) THEN  INC (CptElemPrim [j]);
            ELSE  Ok := FALSE;  INC (CptNoElemPrim [j])  END;
         ELSE
            Ok := PerMaxPowPrime (j);
            IF Ok THEN  INC (CptElemPrim [j])
            ELSE  INC (CptNoElemPrim [j]) END;
            END;
         END;
      IF Ok THEN
         IF i = 1 THEN
            INC (TotEP [j]);
            IF Pow2 OR (NOT PerMax [j]) OR (Orderj [j] = 1)
                  OR MaxPeriod (Maj [j]) THEN
               (* Note: MaxPeriod verifie cond. (b--c) pour per. max.  *)
               (* If power of prime, then j = i = Orderj [j] = 1.      *)
               INC (CptPerMax [j]);
               IF J = 1 THEN
                  (* Tester ce gener. et le conserver si competitif.   *)
                  TestGen (Maj [1], Criterion, VerifyAll, None);
                  CASE Criterion OF
                     Spectral, SpectralL1 : VerifyCategories (S2) |
                     Beyer                : VerifyCategories (Q2) 
                     END
               ELSE
                  (* On memorise ce polynome dans la liste.            *)
                  CreatePoly (P, j);
                  MCopyVect (Maj [j], P^.a, Orderj [j]);
                  END
               END
         ELSE
            Exam (j, i-1);
            END
         END;
   END ExamThisaj;

(****************************************************************************)

PROCEDURE ExamBits 
   ( q    : MScal; 
     j, i, b0, b1, NbBits : INTEGER; 
     Pow2 : BOOLEAN;
     Exam : ProcII
   );
   (* Called by InsideExam (and calls itself recursively) to examine
      all bit patterns with less than NbMaxBits [j] in total,
      that can be obtained by switching from 0 to 1 some of the bits
      of q from bit b0 to bit b1.                                        *)
   VAR
      b : INTEGER;
   BEGIN
   FOR b := b0 TO b1 DO
      MAdd (q, MTwoExp[b], Maj[j,i]);
      ExamThisaj (j, i, Pow2, Exam);
      IF (b > b0) AND (NbBits < NbMaxBits [j]) THEN 
         ExamBits (Maj[j,i], j, i, b0, b-1, NbBits+1, Pow2, Exam) 
         END; 
      MSubtract (Maj[j,i], MTwoExp[b], Maj[j,i]);
      MSubtract (Maj[j,i], MTwoExp[b], Maj[j,i]);
      ExamThisaj (j, i, Pow2, Exam);
      IF (b > b0) AND (NbBits < NbMaxBits [j]) THEN 
         ExamBits (Maj[j,i], j, i, b0, b-1, NbBits+1, Pow2, Exam) 
         END; 
      MAdd (Maj[j,i], MTwoExp[b], Maj[j,i]);
      END
   END ExamBits;

(****************************************************************************)

PROCEDURE InsideExam (j, i, No : INTEGER;   q, sup : MScal;  Exam : ProcII);
   (* Called by ExamRegion or by ExamAllZones for zone nb No.            *)
   VAR
      Pow2 : BOOLEAN;
   BEGIN
   Pow2 := FALSE;
   IF (PerMax [j]) AND (NOT Primemj [j]) AND (M1 [j] = 2) THEN 
      Pow2 := TRUE;   (* m is a power of two: want a mod 8 = 5 only.  *)
      MModulo (q, MEight, MTemp);
      WHILE (NOT MEqual (MTemp, MFive)) DO  
         MInc (q, 1);   MModulo (q, MEight, MTemp);
         END;
      END;
   IF ImplemCond [j] = MaxBits THEN 
      ExamBits (MZero, j, i, 0, HighestBit [j], 1, Pow2, Exam);
      RETURN
      END;
   WHILE (NOT MSmaller (sup, q)) DO
      IF TimeOver () THEN  RETURN  END;
      IF (ImplemCond [j] = AppFact) AND DivQ [No] THEN
         MQuotient (Mmj [j], q, Maj[j,i]);
      ELSE
         MAffect (q, Maj[j,i]);
         END;
      ExamThisaj (j, i, Pow2, Exam);
      IF Pow2 THEN  MInc (q, 8) ELSE  MInc (q, 1) END;
      END;
   END InsideExam;

(****************************************************************************)

PROCEDURE ExamAllZones (j, i : INTEGER);
   (* Used in the "Exhaustive search" case.                                 *)
   (* When J > 1, collects "primitive" polynomials for a given j.           *)
   (* When J = 1, tests all generators in the region.                       *)
   (* Initial call is for i = Orderj [j].                                   *)
   (* Then, the procedure calls itself recursively for smaller i.           *)
   VAR
      Z  : ToZone;
   BEGIN
   IF TimeOver () THEN  RETURN  END;
   Z := bcZone [j, i];
   WHILE Z # NIL DO
      WITH Z^ DO              (* On va examiner toute cette zone.           *)
         (* Mq et MBsup pas var. locales pour eviter les creations repetit. *)
         SupToMScal (Binf, Mq);  SupToMScal (Bsup, MBsup);
         InsideExam (j, i, No, Mq, MBsup, ExamAllZones);
         END;
      Z := Z^.NextZone
      END;
   END ExamAllZones;

(****************************************************************************)

PROCEDURE ExamRegion (j, i : INTEGER);
   (* Used in the "Random search" case.                                     *)
   (* When J > 1, collects "primitive" polynomials for a given j.           *)
   (* When J = 1, tests all generators in the region.                       *)
   (* Initial call is for i = Orderj [j].                                   *)
   (* Then, the procedure calls itself recursively for smaller i.           *)
   BEGIN
   WITH Reg [j,i]^ DO         (* On va examiner toute cette region.         *)
      MAffect (Binf, Mq);     (* Mq n'est pas une var. locale pour eviter   *)
                              (* de la creer a chaque fois.                 *)
      InsideExam (j, i, No, Mq, Bsup, ExamRegion);
      END
   END ExamRegion;

(****************************************************************************)

PROCEDURE ExamCombPoly (jj : Indexj);
   (* Only used when J > 1; examine all combinations of the primitive       *)
   (* polynomials found by ExamRegion or ExamAllZones.                      *)
   VAR
      t  : INTEGER;
      P  : Poly;
   BEGIN
   IF TimeOver () THEN  RETURN  END;
   P := ListPoly [jj];
   WHILE P # NIL DO
      FOR t := 1 TO Orderj [jj] DO  MScalToSup (P^.a [t], aj [jj, t])  END;
      (*  MCopyVect (P^.a, Maj [jj], Orderj [jj]);  *)
      IF jj > 1 THEN
         ExamCombPoly (jj - 1)
      ELSE
         (* Calcule le multiplicateur a du generateur combine, puis teste. *)
         Computea;
         TestGen (a, Criterion, VerifyAll, None);
          CASE Criterion OF
               Spectral, SpectralL1 : VerifyCategories (S2) |
               Beyer                : VerifyCategories (Q2) 
               END
         END;
      P := P^.NextPoly
      END
   END ExamCombPoly;

(****************************************************************************)

PROCEDURE ExamCurrenta;
   (* Tester ce generateur combine et le conserver si competitif.           *)
   (* Appel\'e seulement par testGenFromFile.                               *)
   VAR
      j, i : INTEGER;
   BEGIN
   FOR j := 1 TO J DO
      FOR i := 1 TO Orderj [j] DO
         IF (NOT Equal (aj[j,i], Zero)) THEN
            Divide (mm, aj[j,i], SupT, SupT1);
            IF (ImplemCond [j] = AppFact) AND NOT Smaller (SupT1, SupT) THEN
               (* la condition n'est pas satisfaite *)
               RETURN END
            END
         END;
      IF PerMax [j] THEN
         IF NOT Primemj [j] THEN
            IF NOT PerMaxPowPrime (j) THEN  RETURN  END
         ELSE
            (* On verifie cond. pour periode max.                         *)
            MSetm (Mmj [j]);
            SetFactors (FactmMS1[j], Factr[j], Orderj[j]);
            IF PrimElem (Maj [j]) AND MaxPeriod (Maj [j]) THEN
               INC (CptPerMax [j])
            ELSE
               RETURN
               END
            END
         END
      END;
   MSetm (m);   Computea;
   TestGen (a, Criterion, VerifyAll, None);
   CASE Criterion OF
      Spectral, SpectralL1 : VerifyCategories (S2) |
      Beyer                : VerifyCategories (Q2) 
      END
   END ExamCurrenta;

(**************************************************************************)

PROCEDURE TestGenFromFile;
   (* Examine tous les generateurs d'un fichier .gen.                      *)
   VAR
      i, j, k : INTEGER;
   BEGIN
   k := 1;
   WHILE (k <= NbGenFile) AND (NOT EOF ()) DO
      IF TimeOver () THEN  CloseInput;  RETURN  END;
      FOR j := 1 TO J DO
         FOR i := 1 TO Orderj [j] DO
            ReadSup (aj [j, i], 10);  SupToMScal (aj [j, i], Maj [j, i]);
            ReadLn
            END;
         ReadLn;
         END;
      ExamCurrenta;
      INC (k);
      END
   END TestGenFromFile;

(****************************************************************************)

PROCEDURE CalculNbreGen (j : Indexj);
   (* Calcule le nombre total de generateurs simples (polynomes) examines.  *)
   (* Le resultat sera place dans  TotGen [j].                              *)
   VAR
      Sumji, IntE : LONGINT;
      r, s, LRE   : LONGREAL;
      i           : INTEGER;
      Z           : ToZone;
      E           : SuperInteger;
   BEGIN
   Create (E, 2);
   IF (NOT Exhaust [j]) AND (CptNoElemPrim [j] > 0)  THEN
      (* Il faut evaluer le nb de gen. rejetes parce que     *)
      (* aj [j,k] n'etait pas element primitif.              *)
      r := 1.0;   TotGen [j] := TotEP [j];
      FOR i := 1 TO Orderj [j] - 1 DO
         Z := bcZone [j, i];   s := 0.0;
         WHILE Z # NIL DO
            WITH Z^ DO
               IF PetiteDiff THEN
                  Subtract (Bsup, Binf, E);  SupToLongReal (E, LRE);
                  s := s + p * LRE;
               ELSE
                  s := s + p * LIToLR (H [j]);
                  END;
               END;
            Z := Z^.NextZone;
            END;
         r := r * s;
         END;
      LRE := LIToLR (CptNoElemPrim [j]);   LRE := LRE * r;
      TotGen [j] := TotGen [j] + Round (LRE);
   ELSIF Exhaust [j] THEN
      (* Methode de recherche exhaustive.   *)
      TotGen [j] := 1;
      FOR i := 1 TO Orderj [j] DO
         Z := bcZone [j,i];   Sumji := 0;
         WHILE Z # NIL DO
            Subtract (Z^.Bsup, Z^.Binf, E);   SupToInt (E, IntE);
            Sumji := Sumji + IntE + 1;
            Z := Z^.NextZone;
            END;
         TotGen [j] := Sumji * TotGen [j];
         END;
   ELSE
      (* Pas de periode maximale *)
      TotGen [j] := TotEP [j];
      END;
   Delete (E)
   END CalculNbreGen;

(***************************************************************************)

PROCEDURE CalculerResteInfo;
   (* Calculer les dernieres informations sur les generateurs retenus.     *)
   (* Calculer les d_t ou les q_t si necessaire et pas deja fait.          *)
   (* Refaire les calculs avec bornes sur les erreurs, si necessaire.      *)
   VAR
      Max, i, j : INTEGER;
      G         : Generateur;
      C         : INTEGER;
   BEGIN
   FOR C := NbCat TO 1 BY -1 DO
      G := PireGen[C];
      (* On en voulait NbGen [C] et on en a retenu Caff [C].               *)
      FOR i := 1 TO NbGen[C] - Caff[C] DO G := G^.NextGen END;
      FOR i := 1 TO Caff[C] DO   (* Pour chaque generateur conserve, faire: *)
         IF TimeOver () THEN  
            LatInfo := Criterion;    Verif := NoVerify;
            VerifyAll := Verify0;    VerifyRet := Verify0
            END;
         (*   toST := ValChrono (Timer2, sec);   *)
         WITH G^.Res^ DO
            CASE Criterion OF
               Beyer : DimQ2 := TabDim [C];             (* Dim. max. testee. *)
                  (* Le test de Beyer ayant deja ete fait (critere), on fait *)
                  (* le test spectral si cette information a ete demandee,   *)
                  (* de meme que les verifications si necessaires.           *)
                  IF (LatInfo # Criterion) THEN
                     TestGen (G^.a, Spectral, VerifyRet, None);
                     IF TestCompleted THEN  Max := TabDim [C] 
                     ELSE  Max := Bas^.Dim  END;
                     (* copie les resultats dans le generateur               *)
                     DimD2 := Max;       (* Dimension max. ou on a d_t.      *)
                     FOR j := 1 TO Max DO
                        RD2[j] := D2[j];
                        IF i <= CAST (INTEGER, NormalG^.Maxt) THEN  
                           RS2 [j] := S2 [j]  END
                        END
                     END;
                  IF (VerifyRet # Verify0) THEN
                     TestGen (G^.a, Beyer, VerifyRet, None); (* Verif les q_t.*)
                     IF TestCompleted THEN Max := TabDim [C] 
                     ELSE Max := Bas^.Dim  END;
                     DimQ2 := Max;
                     FOR j := 1 TO Max DO RQ2[j] := Q2[j] END
                     END
              | Spectral, SpectralL1 : DimD2 := TabDim [C]; 
                  (* Le test spectral ayant deja ete fait (critere), fait le *)
                  (* test de Beyer si cette information a ete demandee,      *)
                  (* de meme que les verifications si necessaires            *)
                  IF (LatInfo # Criterion) THEN
                     TestGen (G^.a, Beyer, VerifyRet, None);
                     IF TestCompleted THEN Max := TabDim[C] 
                     ELSE Max := Bas^.Dim  END;
                     (* copie les resultats dans le generateur *)
                     DimQ2 := Max;
                     FOR j := 1 TO Max DO RQ2[j] := Q2[j] END
                     END;
                  IF (VerifyRet # Verify0) THEN
                     TestGen (G^.a, Spectral, VerifyRet, None);
                     IF TestCompleted THEN Max := TabDim[C] 
                     ELSE  Max := Bas^.Dim  END;
                     DimD2 := Max;
                     FOR j := 1 TO Max DO
                        RD2[j] := D2[j];
                        IF i <= CAST (INTEGER, NormalG^.Maxt) THEN  
                           RS2 [j] := S2 [j]  END
                        END
                     END
               END; 
            END; 
         (*  tST := tST + ValChrono (Timer2, sec) - toST;  *)
         G := G^.NextGen
         END; 
      END;  
   END CalculerResteInfo;

(****************************************************************************)

PROCEDURE PrintErrBounds (T : INTEGER);
   (* Calcule et imprime les bornes sur l'ecart entre les points produits   *)
   (* par le generateur combine et le MRG associ\'e, en dimensions 2 \'a T. *)
   (* Pour J > 1.                                                           *)
   VAR
      j, t : INTEGER;
      PLR, m1LR, mjLR, Delt, Deltp, Deltm, B : LONGREAL;
   BEGIN
   Deltp := 0.0;  Deltm := 0.0;
   FOR j := 2 TO J DO
      Subtract (mj [j], mj [1], P);
      IF ODD (j) THEN ChangeSign (P, P) END;
      SupToLongReal (P, PLR);  SupToLongReal (mj [j], mjLR);
      IF Positive (P) THEN
         Deltp := Deltp + PLR * (mjLR - 1.0) / mjLR;
         Deltm := Deltm + PLR / mjLR
      ELSE
         Deltp := Deltp + PLR / mjLR;
         Deltm := Deltm + PLR * (mjLR - 1.0) / mjLR
         END
      END;
   SupToLongReal (mj [1], m1LR);
   Deltm := Deltm / m1LR;   Deltp := Deltp / m1LR;
   IF ABS (Deltp) > ABS (Deltm) THEN
      Delt := ABS (Deltp)
   ELSE
      Delt := ABS (Deltm)
      END;
   WriteString ("   Error bounds (assuming that delta_j = (-1)^{j-1}):");
   WriteLn;  WriteString ("   Delta - = ");  WriteLR (Deltm, 12, 8, 5);
   WriteLn;  WriteString ("   Delta + = ");  WriteLR (Deltp, 12, 8, 5);
   WriteLn;  WriteLn;
   WriteString ('       t      Delta Sqrt{t}');   WriteLn;
   FOR t := 2 TO T DO
      B := Delt * Sqrt (IToLR (t));
      WriteLn;  WriteInt (t, 7);  WriteLR (B, 20, 12, 5)
      END;
   WriteLn;
   END PrintErrBounds;

(****************************************************************************)

PROCEDURE EcrisGen (G : Generateur; IndTabDim : INTEGER);
   (* Imprime les parametres et resultats relatifs a un generateur G.     *)
   (* Appel\'e par WriteSeekRes.                                          *)
   VAR
      i, j, t, dD2, dQ2 : INTEGER;
      x : LONGREAL;
   BEGIN
   FOR j := 1 TO J DO
      IF J > 1 THEN
         WriteString ('  Component ');  WriteInt (j, 2);   WriteLn
         END;
      FOR i := 1 TO Orderj [j] DO
         MAffect (G^.Maj [j,i], MTemp);
         WriteString ('   a_');   WriteInt (i, 1);   WriteString (' = ');
         MWriteScal (MTemp);   WriteLn;
         IF ImplemCond [j] = MaxBits THEN 
            WriteString ('       = ');  
            MWriteScalBin (MTemp);   WriteLn;
            END;
         IF MSmaller (MTemp, MZero) THEN
            WriteString ('       = ');  
            MAdd (MTemp, Mmj [j], MTemp);
            MWriteScal (MTemp);   WriteLn;
            END;
         END;
      END;
   IF J > 1 THEN
      WriteLn;  WriteString ('  Combination: ');   WriteLn;
      FOR i := 1 TO Order DO
         WriteString ('   a_');   WriteInt (i, 1);   WriteString (' = ');
         MWriteScal (G^.a [i]);   WriteLn
         END
      END;
   WriteLn;
   WriteString ('    t     ');
   IF (LatInfo = Spectral) OR (LatInfo = BeyerSpectral) THEN
      WriteString ('       d_t     ')
      END;
   IF (LatInfo = SpectralL1) THEN
      WriteString ('       N_t     ')
      END;
   IF (LatInfo = Beyer) OR (LatInfo = BeyerSpectral) THEN
      WriteString ('       q_t     ')
      END;
   IF (LatInfo # Beyer) THEN
      WriteString ('      S_t ');
      IF InvertCrit THEN WriteString ('(inverse)') END
      END;
   WriteLn;   WriteString ('   ------------------------------------');
   WriteString ('---------------');   WriteLn;

   dD2 := VAL (INTEGER, (G^.Res^.DimD2));
   dQ2 := VAL (INTEGER, (G^.Res^.DimQ2));
   (* On pourrait remplacer IndTabDim par NbCat ci-bas pour avoir         *)
   (* davantage d'information.                                            *)
   FOR t := Order+1 TO TabDim [IndTabDim] DO
      WriteInt (t, 5);   WriteString ( '    ' );
      IF (LatInfo = Spectral) OR (LatInfo = BeyerSpectral) THEN
         WriteLR (Sqrt (G^.Res^.RD2 [t]), 12, 5, 4)   (* d_t *)
         END;
      IF (LatInfo = SpectralL1) THEN
         WriteLR ((G^.Res^.RD2 [t]), 12, 1, 2)         (* N_t *)
         END;
      IF (LatInfo = Beyer) OR (LatInfo = BeyerSpectral) THEN
         WriteLR (Sqrt (G^.Res^.RQ2 [t] ), 12, 5, 4)   (* q_t *)
         END;
      IF (LatInfo # Beyer) AND (t <= dD2) 
            AND (t <= CAST (INTEGER, NormalG^.Maxt))  THEN       (* S_t *)
         x := G^.Res^.RS2 [t];
         IF (LatInfo # SpectralL1) THEN x := Sqrt (x) END;
         IF InvertCrit THEN x := 1.0 / x END;
         WriteLR (x, 14, 5, 4)
         END;
      WriteLn
      END;
   WriteLn;   WriteString ('   Merit = ');
   x := G^.Merit;
   IF (LatInfo # SpectralL1) THEN  x := Sqrt (x) END;
   IF InvertCrit THEN x := 1.0 / x END;
   WriteLR (x, 10, 5, 5);   WriteString ('  = ');
   IF Criterion = Beyer THEN  WriteString ('q_') ELSE  WriteString ('S_') END;
   WriteInt (G^.DimMerit, 1);   WriteLn
   END EcrisGen;

(***************************************************************************)

PROCEDURE WriteLatHead;
   VAR
     i, j: INTEGER;
     S: ARRAY[0..32] OF CHAR;
   (* Imprime une entete pour les resultats.  Appele par LatGen.         *)
   BEGIN
   WriteString (" LATTICE/SPECTRAL TEST ");  WriteLn;
   HostName (S);
   WriteString (' Tests are running on : ');  
   WriteString (S); WriteLn;  WriteLn;
   WriteString (" Generator's components:");  WriteLn;
   WriteString (" Number of components:" );  WriteInt (J, 3);  WriteLn;
   FOR j := 1 TO J DO  WriteDataComponent (j)  END;
   IF J > 1 THEN
      WriteLn;  WriteString (" Combined generator:");  WriteLn;
      WriteString ("   m = ");  MWriteScal (m);   WriteLn;
      WriteString ("   k = ");  WriteInt (Order, 1);    WriteLn;
      IF LatType # PrimePower THEN
         WriteString ("   rho       = ");
         IF Greater (Rho, DixExp50) THEN WriteLn  END;
         WriteSup (Rho, 10, 70);    WriteLn;
         WriteString ("   prod(rho_j)/rho = ");
         WriteSup (LossRho, 10, 70);    WriteLn;
         END;
      FOR i :=1 TO Order DO
         WriteString ('   a_');  WriteInt(i, 1);
         WriteString (' = ');   MWriteScal (a [i]);   WriteLn;
         END
      END;
   WriteLn;  WriteString (" Lattice type: ");
   CASE LatType OF
        Full        : WriteString ('Full');
      | Recurrent   : WriteString ('Recurrent');
      | Orbit       : WriteString ('Orbit');
      | PrimePower : WriteString ('PrimePower')
      END;
   IF ((LatInfo = Spectral) OR (LatInfo = BeyerSpectral)) THEN
      WriteLn;   WriteString (" Bound used to define S_t: "); 
      CASE Critere2 OF 
          BestLat   : WriteString ("BestLat") |
          Minkowski : WriteString ("Minkowski") |
          Laminated : WriteString ("Laminated") |
          Rogers    : WriteString ("Rogers")
          END;
      END;
   WriteLn;  WriteString ('-------------------------------------');
   WriteLn;  WriteLn;
   END WriteLatHead;

(****************************************************************************)

PROCEDURE WriteLatHeadTex;
   (* Imprime une entete pour les resultats format TEX.  Appele par LatGen. *)
   VAR
     i, j: INTEGER;
     S: ARRAY[0..31] OF CHAR;
   BEGIN
   WriteString ("\parindent = 0pt ");  WriteLn;
   WriteString (" LATTICE/SPECTRAL TEST \\");  WriteLn;
   HostName (S);
   WriteString (' Tests are running on : ');  
   WriteString (S); WriteString('\\');  WriteLn;  WriteLn;
   WriteString (" Generator's components:\\");  WriteLn;
   WriteString (" Number of components:" );  WriteInt (J, 3);
   WriteString ("\\");  WriteLn;
   FOR j := 1 TO J DO  WriteDataComponent (j)  END;
   IF J > 1 THEN
      WriteLn;  WriteString (" Combined generator:\\");  WriteLn;
      WriteString ("   $m =$ ");  MWriteScal (m);   WriteString (" \\");  
      WriteLn;
      WriteString ("   $k =$ ");  WriteInt (Order, 1);   WriteString ("\\");  
      WriteLn;
      IF LatType # PrimePower THEN
         WriteString ("   $\rho =$ ");
         IF Greater (Rho, DixExp50) THEN WriteLn  END;
         WriteSup (Rho, 10, 70);   WriteString ("\\");   WriteLn;
         WriteString ("   $(\Prod_j \rho_j) /\rho =$ ");
         WriteSup (LossRho, 10, 70);    WriteString ("\\");  WriteLn;
         END;
      FOR i :=1 TO Order DO
         WriteString ('   $a_');  WriteInt(i, 1);
         WriteString (' =$ ');   MWriteScal (a [i]);   WriteString ("\\");  
         WriteLn;
         END
      END;
   WriteString ("\\");  WriteLn;  WriteString (" Lattice type: ");
   CASE LatType OF
        Full       : WriteString ('Full \\');
      | Recurrent  : WriteString ('Recurrent \\');
      | PrimePower : WriteString ('PrimePower \\')
      END;
   IF ((LatInfo = Spectral) OR (LatInfo = BeyerSpectral)) THEN
      WriteLn;   WriteString (" Bound used to define $S_t$: "); 
      CASE Critere2 OF 
          BestLat   : WriteString ("BestLat") |
          Minkowski : WriteString ("Minkowski") |
          Laminated : WriteString ("Laminated") |
          Rogers    : WriteString ("Rogers")
          END;
      END;
   WriteLn; 
   IF Streams THEN
      WriteString('\hrule  \\');  WriteLn; WriteString("\ \\");  END;
   WriteLn;
   END WriteLatHeadTex;

(****************************************************************************)

PROCEDURE WriteDataComponent (j : Indexj);
   (* Imprime toutes les donnees relatives a la composante j.               *)
   VAR
     i: INTEGER;
   BEGIN
   IF J > 1 THEN
      WriteLn;
      WriteString (' Component ');  WriteInt (j, 2);  
      IF Tex THEN WriteString (" \\ ") END;  WriteLn 
      END;
   WriteString ('   Type of generator considered : ');
   IF TypeGen [j] = MRG THEN  
      WriteString ('MRG')
   ELSIF TypeGen [j] = MWC THEN 
      WriteString ('MWC')
   ELSE 
      WriteString ('UNDEFINED !')  
      END;
   WriteLn;
   WriteString ('   Modulus  m = ');  WriteSup (mj [j], 10, 70);
   IF (TroisChiffres [j]) AND (M2 [j] > 1) THEN
      WriteString (' ( = '); WriteLI (M1 [j], 1);
      WriteString ('^');     WriteLI (M2 [j], 1);
      IF M3 [j] # 0 THEN
         IF M3 [j] > 0 THEN  WriteString (' + ') ELSE WriteString (' ')  END;
         WriteLI (M3 [j], 2);
         END;
      WriteString (' )')
      END;
   IF Tex THEN WriteString (" \\ ") END;   WriteLn;
   WriteString ('   Order    k = ');  WriteInt (Orderj [j], 1);
   IF LatType # PrimePower THEN
      IF Tex THEN WriteString (" \\ ") END;   WriteLn;
      WriteString ('   n_j        = ');  WriteSup (nj [j], 10, 70);
      PowerSupInt (mj [j], Orderj [j], SupT3);
      Subtract (SupT3, One, SupT3);
      WriteLn;  WriteString ('   rho_j = (m_j)^k_j-1 = ');
      WriteSup (Rhoj [j], 10, 70);
      END;
   IF (Primemj [j]) THEN
      IF Tex THEN WriteString (" \\ ") END;   WriteLn;
      WriteString ('   Factors of m-1   : ');
      CASE DecomposeM [j] OF
         Decomp      : WriteString (' Decomp ') |
         DecompWrite : WriteString (' DecompWrite ');
                       WriteString (FichmMS1 [j]) |
         READ        : WriteString (' Read ')
         END;
      IF Tex THEN WriteString (" \\ ") END;   WriteLn;
      WriteString ('   Factors of r     : ');
      CASE DecomposeR [j] OF
         Decomp      : WriteString (' Decomp ') |
         DecompWrite : WriteString (' DecompWrite ');
                       WriteString (Fichr [j]) |
         READ        : WriteString (' Read ') |
         Prime       : WriteString (' Prime ')
         END
      END;
   IF Tex THEN WriteString (" \\ ") END;   WriteLn;

   IF ReadGenFromFile THEN
      WriteString ('   Generators read from : ');
      WriteString (FichGen);   WriteString ('.gen');  
      IF Tex THEN WriteString (" \\ ") END;   WriteLn;
   ELSIF Seek THEN
      FOR i := 1 TO Orderj [j] DO
         IF i = 1 THEN  WriteString ('   Bounds : a')
         ELSE  WriteString ('            a')  END;
         WriteInt (i, 1);  WriteString (' from : ');
         WriteSup (bj [j,i], 10, 70);
         WriteLn;   WriteString ('                 to : ');
         WriteSup (cj [j,i], 10, 70); 
         IF Tex THEN WriteString (" \\ ") END;   WriteLn;
         END;
      WriteString ('   Search method                      : ');
      IF Exhaust [j] THEN
         WriteString ('EXHAUST ');
         IF Tex THEN WriteString (" \\ ") END;   WriteLn;
      ELSE
         WriteString ('RANDOM ');
         IF Tex THEN WriteString (" \\ ") END;   WriteLn;
         WriteString ('      Sampling : Numbers of subregions = ');
         WriteLI (CptRegions [j], 1);
         IF Orderj [j] > 1 THEN  WriteString (',  H = ');
         WriteLI (H [j], 1)  END;
         WriteString (',  Hk = ');  WriteLI (Hk [j], 1);
         IF Tex THEN WriteString (" \\ ") END;   WriteLn;
         END;
      WriteString ('   Implementation condition           :');
      CASE ImplemCond [j] OF
         AppFact :
            WriteString (' a_i (m mod a_i) < m')
       | MaxBits :
            WriteString (' Max. of ');  WriteLI (NbMaxBits [j], 1);
            WriteString (' bits in a_i')
       | NoCond :
            WriteString (' NoCond')
         END;
      IF Tex THEN WriteString (" \\ ") END;   WriteLn;
      WriteString ('   Maximum period required            : ');
      IF PerMax [j] THEN WriteString ('YES') ELSE WriteString ('NO') END;
      IF Tex THEN WriteString (" \\ ") END;   WriteLn
   ELSE
      FOR i := 1 TO Orderj [j] DO
         WriteString ('   a_');  WriteInt(i, 1);
         WriteString (' = ');   WriteSup (aj [j,i], 10, 70); 
         IF Tex THEN WriteString (" \\ ") END;   WriteLn;
         END
      END;
   END WriteDataComponent;

(****************************************************************************)

PROCEDURE WriteStatComponent (j : Indexj);
   (* Imprime les statistiques de la recherche relative a la composante j.  *)
   (* Appele par WriteSeekRes.                                              *)
   BEGIN
   IF J > 1 THEN  WriteString (' Component ');  WriteInt (j, 2);  WriteLn  END;
   IF Primemj [j] THEN
      WriteString ('   Values of a');   WriteInt (Orderj [j], 1);
      WriteString (' tried                    : ');
      WriteLI (CptElemPrim [j] + CptNoElemPrim [j], 10);   WriteLn;
      WriteString ('   Values of a'); WriteInt (Orderj [j], 1);
      WriteString (' primitive element        : ');
      WriteLI (CptElemPrim [j], 10);   WriteLn;
      WriteString ('   Polynomials with a');  WriteInt (Orderj [j], 1);
      WriteString (' primitive element : ');  WriteLI (TotEP [j], 10);
      WriteLn;
      WriteString ('   Primitive polynomials                 : ');
      WriteLI (CptPerMax [j], 10);    WriteLn;
      (*
      IF NOT ReadGenFromFile THEN
         WriteString ('   Nb. of polynomials to examine         : ');
         CalculNbreGen (j);   WriteLI (TotGen [j], 10);
         IF ApproxTotGen [j] THEN WriteString (' (approx.)') END
         END
      *)
   ELSE
      WriteString ('   Polynomials examined                  : ');
      WriteLI (TotEP [j], 10);
      END;
   WriteLn;
   END WriteStatComponent;

(****************************************************************************)

PROCEDURE WriteTabBest (l : LONGINT;  G : Generateur);
   VAR
      j, i, t : LONGINT;
      Mins : LONGREAL;
   BEGIN
   FOR j := 1 TO J DO
      IF (l = 1) OR (J > 1) THEN
         WriteString (" $");  WriteLI (M1 [j], 1);
         WriteString ("^{");  WriteLI (M2 [j], 1);   WriteString ("}");
         IF M3 [j] # 0 THEN
            IF M3 [j] > 0 THEN  WriteString ('+') ELSE WriteString (' ')  END;
            WriteLI (M3 [j], 2);
            END;
         (* WriteString (" = ");  WriteSup (mj [j], 10, 50 );  *)  
         WriteString ("$");
         IF (ImplemCond [j] = AppFact) THEN 
            WriteString (" & A")  
         ELSIF (ImplemCond [j] = MaxBits) THEN 
            WriteString (" & B")  
         ELSE 
            WriteString (" & X")  
            END;
         WriteLn;
         END;
       WriteString ("           ");
       FOR i := 1 TO Orderj [j] DO
         WriteString (" & ");  MWriteScal (G^.Maj [j,i]);
         END;
      IF j < J THEN
         FOR t := 1 TO NbCat DO  WriteString (" &")  END;
         WriteString (" \\");  WriteLn;
         END;
      END;
   IF (J = 1) AND (Order = 1) THEN
      IF (LatType = PrimePower) THEN
         Subtract (mjRed[1], One, SupT1);
         MScalToSup (G^.Maj [1,1], SupT2);
         PowerMod (SupT2, SupT1, mj[1], SupT3);
         MultMod (SupT2, SupT3, mj[1], SupT1);
         IF Equal (SupT1, One) THEN
            WriteString (", ");   WriteSup (SupT3, 10, 50);
            END;
      ELSIF (Primemj [1]) AND (LatType = Full) THEN
         Subtract (mm, Two, SupT1);
         MScalToSup (G^.Maj [1,1], SupT2);
         PowerMod (SupT2, SupT1, mm, SupT3);
         MultMod (SupT2, SupT3, mm, SupT1);
         IF Equal (SupT1, One) THEN
            WriteString (", ");   WriteSup (SupT3, 10, 50);
            END;
         END; 
   ELSE
      WriteLn
      END;
   MaxDim := TabDim[NbCat];   Mins2 [l] := 0.0;
   TestGen (G^.a, Spectral, VerifyRet, None);
   Mins := 2.0;   TabDim [0] := MinDim-1;
   FOR j := 1 TO NbCat DO
      FOR t := (1 + TabDim[j-1]) TO TabDim[j] DO
         (*  WriteLI (t, 4);   WriteLR (Sqrt (S2 [t]), 12, 5, 1);  WriteLn;  *)
         IF (S2 [t] < Mins) THEN  Mins := S2 [t] END;
         END;
      IF (LatInfo # SpectralL1) THEN  Mins := Sqrt (Mins) END;
      IF InvertCrit THEN Mins := 1.0 / Mins END;
      WriteString (" & ");   WriteLR (Mins, 7, 5, 1);
      IF j=l THEN  WriteString ("\a") ELSE WriteString ("  ") END;
      END;
   WriteString(" \\");  WriteLn;
   END WriteTabBest;

(****************************************************************************)

PROCEDURE WriteSeekHead;
   (* Imprime l'entete et les donnees pour un "seek".                       *)
   (* Ecrit aussi les factorisations dans les fichiers si necessaire.       *)
   VAR
      C, j : LONGINT;
   BEGIN
   HostName (S);
   WriteString (' Tests are running on : ');  
   WriteString (S);  WriteLn;  WriteLn;
      IF J = 1 THEN
         WriteString (' SEARCH FOR GOOD MRGs OF ORDER ');
         WriteLI (Order, 1);   WriteLn;
      ELSE
         WriteString (' SEARCH FOR GOOD COMBINED MRGs with ');
         WriteLI (J, 1);  WriteString (' components.');   WriteLn;
         END;
      WriteString (' -----------------------------------------');
      WriteLn;   WriteLn;

      (* DONNEES *)
      WriteString (' DATA');  WriteLn;  WriteString (' ----');  WriteLn;
      FOR j := 1 TO J DO  WriteDataComponent (j);  WriteLn  END;

      IF J > 1 THEN
         WriteString (" Combination:");  WriteLn;
         WriteString ("   Modulus m = ");  
         IF Greater (Rho, DixExp50) THEN WriteLn  END;
         WriteSup (mm, 10, 70);  WriteLn;
         WriteString ("   Order   k = ");  WriteInt (Order, 1);    WriteLn;
         IF LatType # PrimePower THEN
            WriteString ("   rho       = ");
            IF Greater (Rho, DixExp50) THEN WriteLn  END;
            WriteSup (Rho, 10, 70);    WriteLn;
            WriteString ("   prod(rho_j)/rho = ");
            WriteSup (LossRho, 10, 70);    WriteLn;
            END;
         PrintErrBounds (MaxDim);   WriteLn;
         END;
      WriteString ('   Merit criterion(s)                 : ');
      FOR C := 1 TO NbCat DO
         IF NOT MaximCat [C] THEN WriteString ("-") END;
         IF Criterion = Beyer THEN
            WriteString ('Q_');   WriteInt (TabDim[C], 1);
         ELSIF (Criterion = Spectral) OR (Criterion = SpectralL1) THEN
            WriteString ('M_');
            IF TabDim [C] <= CAST (INTEGER, NormalG^.Maxt) THEN
               WriteInt (TabDim [C], 1)
            ELSE
               WriteInt (NormalG^.Maxt, 1)
               END;
            END;
         WriteString (" ");
         END;
      IF Criterion = Spectral THEN
         WriteLn;  WriteString ("     (with "); 
         CASE Critere2 OF 
            BestLat   : WriteString ("BestLat") |
            Minkowski : WriteString ("Minkowski") |
            Laminated : WriteString ("Laminated") |
            Rogers    : WriteString ("Rogers")
            END;
         WriteString (" bound)"); 
         END;
      WriteLn;
      IF NOT Exhaust [j] THEN
         WriteString ('   Seeds for RNG                      : ');
         WriteLI (Seed1, 1);
         WriteString (',  ');   WriteLI (Seed2, 1);  WriteLn;
         END;
      WriteString ('   Verify Branch-and-bound            : ');
      CASE Verif OF
           VerifyAll2      : WriteString ('VerifyAll2');
         | VerifyRetained2 : WriteString ('VerifyRetained2');
         | VerifyAll3      : WriteString ('VerifyAll3');
         | VerifyRetained3 : WriteString ('VerifyRetained3');
         | NoVerify        : WriteString ('NoVerify');
         END;
      WriteLn;
      WriteString ('   Maximum nodes in branch-and-bound  : ');
      WriteLI (MaxNodesBB, 1); WriteLn;
      WriteString ('   Lattice Type                       : ');
      CASE LatType OF
           Full       : WriteString ('Full');
         | Recurrent  : WriteString ('Recurrent');
         | PrimePower : WriteString ('PrimePower')
         END;
      WriteLn;
      IF Lacunary THEN
         WriteString (" Lacunary indices:");  WriteLn;
         END;
      WriteLn;
   END WriteSeekHead;

(****************************************************************************)

PROCEDURE WriteSeekRes;
   (* Imprime les r\'esultats d'un "seek".                                  *)
   VAR
      G, GG      : Generateur;
      Gen        : ARRAY [1..MaxNbGen] OF Generateur;
      NGen, j, k : LONGINT;
      l          : LONGINT;
      machine    : ARRAY[0..255] OF CHAR;
   BEGIN
      CalculerResteInfo;
      WriteString (' RESULTS ');  WriteLn;  WriteString (' -------');  WriteLn;
      IF TropLong THEN
	 WriteString ("** Warning: Program aborted, reached time limit. **");
         WriteLn;
         WriteString ("     There will be no verification of results.");
         WriteLn;   WriteString ("          time limit : ");
         WriteLR (TempsLimite, 10, 2, 2);
         WriteString (" hour(s) ");   WriteLn;
         END;
      FOR j := 1 TO J DO  WriteStatComponent (j)  END;   WriteLn;

      HostName (machine);
      WriteString ('   Tests were performed on               : ');  
      WriteString (machine);  WriteLn; 
      WriteString ('   Total CPU time (after setup)          : ');
   (*   WriteChrono (Timer2, hms);  WriteLn;
   *)   WriteLn;

      FOR l := 1 TO NbCat DO
         WriteLn;  WriteString 
            (' ----------------------------------------------------------'); 
         WriteLn;
         WriteLn;  WriteString (' Merit criterion          : ');
         IF NOT MaximCat [l] THEN WriteString ("-") END;
         IF Criterion = Beyer THEN
            WriteString ('Q_');   WriteInt (TabDim[l], 1);
         ELSE
            WriteString ('M_');
            IF TabDim [l] <= CAST (INTEGER, NormalG^.Maxt) THEN
               WriteInt (TabDim [l], 1)
            ELSE
               WriteInt (NormalG^.Maxt, 1)
               END;
            END;
         WriteString (" ");
         WriteLn; WriteString (' Lower bound              : ');
         WriteLR (MinMerit[l], 6, 4, 2); 
         WriteLn; WriteString (' Upper bound              : ');
         WriteLR (MaxMerit[l], 6, 4, 2); 
         WriteLn; WriteString (' Nb. Gener. tried in cat. : ');
         WriteInt (NbTried[l], 1); 
         WriteLn; WriteString (' Nb. Generators conserved : ');
         WriteInt (Caff[l], 1);  WriteLn;  WriteLn;

         (* Ecriture des generateurs *)
         NGen := 1;   G := PireGen[l];
         WHILE G # NIL DO  Gen [NGen] := G;   G := G^.NextGen;  INC (NGen) END;
         (* On ecrit les generateurs dans l'ordre inverse de la liste,     *)
         (* c.-a-d. du meilleur au pire.                                   *)
         FOR k := NGen-1 TO NbGen[l] - Caff[l] + 1 BY -1 DO
            WriteLn;  WriteInt (NGen - k, 1);  WriteString ('. ');  WriteLn;
            EcrisGen (Gen [k], l)  (* Ecrit les resultats pour ce generat. *)
            END;
         END;
      IF (LatInfo # Beyer) THEN 
         WriteLn;  WriteLn;   WriteString 
            (' ----------------------------------------------------------'); 
         WriteLn;
         WriteString ("\hline");  WriteLn;
         FOR l := 1 TO NbCat DO
            IF Caff [l] > 0 THEN
               G := PireGen[l];  GG := G;
               WHILE G # NIL DO  GG := G;   G := G^.NextGen  END;
               WriteTabBest (l, GG);
               END;
            END;
         END;
      FOR j := 1 TO J DO
         IF EcriremMS1 [j] THEN EcrireFact (FactmMS1 [j], FichmMS1 [j]) END;
         IF Ecrirer [j]    THEN EcrireFact (Factr [j], Fichr [j]) END
         END;
   END WriteSeekRes;

(****************************************************************************)

PROCEDURE WriteSeekGen;
   (* Stocke les r\'esultats d'un "seek" dans un fichier ".gen".     *)
   VAR
      G          : Generateur;
      Gen        : ARRAY [1..MaxNbGen] OF Generateur;
      NGen, i, j, k : LONGINT;
      H          : Generateur;
      l, p, q, r : LONGINT;
      TotCaff    : LONGINT;
      MajExist   : BOOLEAN;
   BEGIN
   (* Creer le fichier .gen et ecrire les generateurs dedans.     *)
   Concat (S, FName, '.gen');  OpenAsOutput (S);  (*  GetOutput (FOut); *)
   WriteInt (J, 1);  WriteLn;

      FOR j := 1 TO J DO
         WriteSup (mj [j], 10, 70);
         IF TroisChiffres [j] THEN
            WriteString (' ( = '); WriteLI (M1 [j], 1);
            WriteString ('^');     WriteLI (M2 [j], 1);
            IF M3 [j] >= 0 THEN WriteString (' + ') END;
            WriteLI (M3 [j], 1);  WriteString (' )')
         ELSE
            WriteSup (mj [j], 10, 70);
            END;
         WriteLn;  
         WriteInt (Orderj [j], 5);  WriteLn
         END;
      TotCaff := 0;
      FOR l := 1 TO NbCat DO
         TotCaff := TotCaff + Caff[l];
         END;
      WriteInt (TotCaff, 5);  
      (* WriteString ('  Borne sup. sur nb. de gen a lire'); *)  WriteLn;

      FOR l := 1 TO NbCat DO
         NGen := 1;   G := PireGen[l];
         WHILE G # NIL DO  Gen [NGen] := G;   G := G^.NextGen;  INC (NGen) END;
         (* On ecrit les generateurs dans l'ordre inverse de la liste,        *)
         FOR k := NGen - 1 TO (NbGen [l] - Caff [l] + 1) BY -1 DO
            FOR j := 1 TO J DO
               FOR i := 1 TO Orderj [j] DO
                  (* Parcourir toutes les listes precedentes pour verifier   *)
                  (* si la valeur existe deja.                               *)
                  p := 1;  MajExist := FALSE;
                  WHILE (p < l) AND (NOT MajExist) DO
                     H := PireGen[p];
                     WHILE (H # NIL) AND (NOT MajExist) DO
                        q := 1;
                        WHILE (q <= J ) AND (NOT MajExist) DO
                           r := 1;
                           WHILE (r <= Orderj [q]) AND (NOT MajExist) DO
                              MajExist := MEqual(H^.Maj[q,r], Gen [k]^.Maj[j,i]);
                              INC (r);
                              END;
                           INC (q);
                           END;
                        H := H^.NextGen;
                        END;
                     INC (p);
                     END;
                  MWriteScal (Gen [k]^.Maj[j,i]);  WriteLn;  WriteLn;
                  END;
               END
            END;
         END;
   CloseOutput;
   END WriteSeekGen;

(****************************************************************************)

PROCEDURE SetupSeekGen;
   (* Creation des listes ordonnees des NbGen [C] meilleurs generateurs.   *)
   (* Initialisation des zones de recherche.  Appel\'e par SetUp.          *)
   VAR
      G, GSuiv : Generateur;
      C, i, j  : INTEGER;
   BEGIN
   FOR C := 1 TO NbCat DO
      Caff[C] := 0;   NbTried[C] := 0;
      CreateGenerateur (G);   PireGen[C] := G;
      IF NOT MaximCat [C] THEN G^.Merit := 1.0 END;
      FOR j := 1 TO NbGen [C] - 1 DO
         CreateGenerateur (GSuiv);  G^.NextGen := GSuiv;  G := GSuiv;
         IF NOT MaximCat [C] THEN GSuiv^.Merit := 1.0 END;
         END;
      FOR i := (1 + TabDim [C-1]) TO (TabDim [C]) DO
         IF Criterion = Beyer THEN
            Minq2[i] := MinMerit[C] * MinMerit[C];  Mins2[i] := 0.0;
         ELSIF Criterion = Spectral THEN
            Mins2[i] := MinMerit[C] * MinMerit[C];  Minq2[i] := 0.0;
         ELSIF Criterion = SpectralL1 THEN
            Mins2[i] := MinMerit[C];  Minq2[i] := 0.0;
            END;
         END
      END;
   IF NOT ReadGenFromFile THEN
      FOR j := 1 TO J DO
         ListPoly [j] := NIL;
         FOR i := 1 TO Orderj [j] DO  InitZones (j, i)  END;
         END
      END;
   END SetupSeekGen;

(****************************************************************************)

PROCEDURE Setup;
   (* Lectures des donnees et initialisations.  Pour SeekGen ou LatGen.    *)
   (* Initialise REDBAS et MRG.                                            *)
   VAR
     j: INTEGER;
   BEGIN
   TropLong := FALSE;
   FOR j := 1 TO MaxJ DO
      CptElemPrim [j] := 0;     CptPerMax [j] := 0;   TotEP [j] := 0;
      CptNoElemPrim [j] := 0;   CptRegions [j] := 0;  PerMax [j] := FALSE;
      ApproxTotGen [j] := FALSE;
      END;

   GetInput (stdIn);   GetOutput (stdOut);
   (* Lecture du nom du fichier des donnees et des resultats.  *)
   ParamToString (1, FName);  Concat (S, FName, '.dat');  OpenAsInput (S);
   SaisieDonnees;
   InitNormaliz (NormalG, "Normaliz de LATIO", UsedNorm, Critere2, 1.0,
                 MaxDim, m, Order);

   InitREDBAS (MaxDim);

   IF (VerifyRet = Verify2) THEN  InitREDBAS2 (MaxDim)  END;
   IF LatType # PrimePower THEN
      SupToMScal (mm, m);
      InitMRG (m, Order, MaxDim);
      END;

   IF Seek THEN SetupSeekGen END;

   IF ReadGenFromFile THEN ReadGenFile END;
   InitChrono (Timer2);
   END Setup;

(*****************************************************************************)

PROCEDURE LatGen;
   (* Teste un generateur particulier.                                      *)
   BEGIN
   Seek := FALSE;   Setup;   CloseInput;
   CASE ResultForm OF
      LTerminal : Out := CurOut;
    | RES       : Out := CurOut;      Concat (S, FName, ".res");
    | TEX       : Out := CurOutTex;   Concat (S, FName, ".tex");  Tex := TRUE;
      END;
   IF ResultForm # LTerminal THEN OpenAsOutput (S); (* GetOutput (FOut) *) END;
   Computea;
   IF Tex THEN  WriteLatHeadTex  ELSE  WriteLatHead END;
   TestGen (a, LatInfo, VerifyRet, Out);
   CloseOutput
   END LatGen;

(*****************************************************************************)

PROCEDURE SeekGen;
   (* Effectue une recherche pour de bons generateurs.                       *)
   VAR
      j, SaveMaxDim : INTEGER;   region : LONGINT;
   BEGIN
   Seek := TRUE;   Setup;   CloseInput;   Out := CurOut;
   IF (ResultForm = RES) OR (ResultForm = RESGEN) THEN
      Concat (S, FName, '.res');  OpenAsOutput (S);  (*  GetOutput (FOut); *)
      END;
   IF (ResultForm # GEN) THEN   WriteSeekHead  END;
   SaveMaxDim := 0;
   IF (Criterion = Spectral) AND (MaxDim > CAST (INTEGER, NormalG^.Maxt)) THEN
      SaveMaxDim := MaxDim;   MaxDim := NormalG^.Maxt;
      END;
   IF ReadGenFromFile THEN
      TestGenFromFile;  CloseInput
   ELSE
      FOR j := 1 TO J DO
         IF (PerMax [j]) AND (Primemj [j]) THEN
            MSetm (Mmj [j]);
            SetFactors (FactmMS1[j], Factr[j], Orderj[j])
            END;
         FOR region := 1 TO NbReg [j] DO
            IF TimeOver () THEN  WriteSeekRes;  RETURN  END;
            IF Exhaust [j] THEN
               ExamAllZones (j, Orderj [j]);
               WriteString (" Exhaustive search completed for j = ");  
               WriteInt (j, 1);  WriteLn;  WriteLn
            ELSE
               (* Choisir une region au hasard et l'examiner au complet.  *)
               ChoisirBornes (j);  ExamRegion (j, Orderj [j])
               END
            END
         END;
      (* Dans le cas J > 1, on examine toutes les combinaisons des        *)
      (* polynomes recueillis.                                            *)
      IF J > 1 THEN 
         WriteString ('   Time to find the primitive polynomials: ');
    (*     WriteChrono (Timer2, hms); *) WriteLn;   WriteLn;
         MSetm (m);  ExamCombPoly (J) 
         END;
      END;
   IF (Criterion = Spectral) AND (SaveMaxDim > CAST (INTEGER, NormalG^.Maxt)) THEN
      MaxDim := SaveMaxDim;
      END;
   IF (ResultForm # GEN) THEN  WriteSeekRes  END;  
   IF (ResultForm = RES) OR (ResultForm = RESGEN) THEN  CloseOutput END;
                                        (* Fermeture du fichier ".res".  *)
   IF (ResultForm = GEN) OR (ResultForm = RESGEN) THEN  WriteSeekGen  END;
   END SeekGen;

(*****************************************************************************)

PROCEDURE CalcLaIndicesStreams (s, w : LONGINT);
   (* Calcule les indices lacunaires par groupe de s, espace de 2^k      *)
   VAR
      La1, s1, t : LONGINT;
   BEGIN
   La1 := s;   PowerSupInt (Two, w, SupT1);
   WriteString ("2^w = ");  WriteSup (SupT1, 10, 70);  WriteLn;
   IF (w = 0) THEN
      Lacunary := FALSE;
      IF MinDim <= Order THEN  MinDim := Order + 1  END;
      RETURN
   ELSE
      Lacunary := TRUE
      END;
   t := 1;   IntToSup (0, SupT);
   WHILE TRUE DO
      FOR s1 := 0 TO (La1-1) DO
         IF t <= MaxDim THEN
            IntToSup (s1, h);  Add (SupT, h, h);
            SupToBScal (h, LacI [t]);  INC (t)
         ELSE
            RETURN
            END
         END;
      Add (SupT, SupT1, SupT);
      END;
   END CalcLaIndicesStreams;

(*****************************************************************************)

PROCEDURE LatGenStreams;
   (* Teste une serie de generateurs.                                    *)
   VAR
     s, w, t1, t2, s1, s2 : LONGINT;
     Merit1, Merit2       : LONGREAL;
     Minqt, MinSt         : ARRAY [0..255] OF LONGREAL;
     tq, sq, tS, sS       : ARRAY [0..255] OF LONGINT;
     i	       	          : INTEGER;
     wmin, wmax, smax     : LONGINT;
   BEGIN
   Streams  := TRUE;
   Seek     := FALSE; 
   Lacunary := TRUE;
   Setup;
   ReadInt (wmin);   ReadInt (wmax);   ReadInt (smax);   ReadLn;
   IF (wmin < 1) OR (wmax > 255) THEN
      ErrorHalt (" wmin or wmax outside range.");
      END;
   CloseInput;

   CASE ResultForm OF
      LTerminal : Out := CurOut;
    | RES       : Out := CurOut;      Concat (S, FName, ".res");
    | TEX       : Out := CurOutTex;   Concat (S, FName, ".tex");  Tex := TRUE;
     END;
   IF ResultForm # LTerminal THEN  
      OpenAsOutput (S);   (* GetOutput (FOut) *)
      END;
   Computea;
   IF Tex THEN WriteLatHeadTex ELSE WriteLatHead; END;
   FOR w := wmin TO wmax DO
      Merit1 := 1.0;   Merit2 := 1.0;  t1 := 0;  s1 := 0;  t2 := 0;  s2 := 0;
      FOR s := 1 TO smax DO
         WriteString ("w = ");  WriteLI (w, 8); 
         WriteString (",     s = ");   WriteLI (s, 8);   WriteLn;
         CalcLaIndicesStreams (s, w);
         TestGen (a, LatInfo, VerifyRet, Out);
         (*  TestGen (a, BeyerSpectral, VerifyRet, Out);  *)
         WriteLn;  WriteLn;
         FOR i := Order+1 TO MaxDim DO
            IF (LatInfo = BeyerSpectral) OR (LatInfo = Beyer) THEN 
               IF (Q2[i] < Merit1) THEN  
                  Merit1 := Q2[i];   t1 := i;   s1 := s;
                  END;
               END;
            IF (i <= INT(NormalG^.Maxt)) THEN
               IF (S2 [i] < Merit2) THEN  
                  Merit2 := S2 [i];  t2 := i;   s2 := s
                  END;
               END
            END;
         END;
      WriteLn;  WriteLn;
      WriteString ("----------------------------------------------------");
      WriteLn;  WriteLn;
      MinSt [w] := Sqrt (Merit2);  tS [w] := t2;  sS [w] := s2;
      IF (LatInfo = BeyerSpectral) OR (LatInfo = Beyer) THEN 
         Minqt [w] := Sqrt (Merit1);  tq [w] := t1;  sq [w] := s1;  
         WriteString ("Minimal value of q_t:");
         WriteLR (Sqrt (Merit1), 14, 8, 2);
         WriteString ("    t = ");   WriteLI (t1, 4);   
         WriteString ("    s = ");   WriteLI (s1, 4);   WriteLn;
         END;
      WriteString ("Minimal value of S_t:");
      WriteLR (Sqrt (Merit2), 14, 8, 2);
      WriteString ("    t = ");   WriteLI (t2, 4);   
      WriteString ("    s = ");   WriteLI (s2, 4);   WriteLn;
      WriteLn;   WriteLn;
      WriteString ("----------------------------------------------------");
      WriteLn;   WriteLn;
      END;

   WriteString ("    w      min S_t      t*S   s*S  ");
   IF (LatInfo = BeyerSpectral) OR (LatInfo = Beyer) THEN 
      WriteString ("  min q_t   t*q    s*q ");
      END;
   WriteLn;  WriteLn;
   FOR w := wmin TO wmax DO
      WriteLI (w, 5);  WriteString (" &");
      WriteLR (MinSt [w], 12, 6, 1);   WriteString (" &");  
      WriteLI (tS [w], 5);  WriteString (" &");  
      WriteLI (sS [w], 5);  WriteString (" \\");  WriteLn;
      IF (LatInfo = BeyerSpectral) OR (LatInfo = Beyer) THEN 
         WriteLR (Minqt [w], 12, 6, 1);   WriteString (" &");
         WriteLI (tq [w], 5);  WriteString (" &");  
         WriteLI (sq [w], 5);  WriteString (" &");
         END
      END;
   CloseOutput;
   END LatGenStreams;

(*****************************************************************************)


BEGIN
Create (Zero, 1);   IntToSup (0, Zero);
Create (One, 1);    IntToSup (1, One);
Create (Two, 1);    IntToSup (2, Two);
Create (Four, 1);   IntToSup (4, Four);
Create (Five, 1);   IntToSup (5, Five);
Create (Eight, 1);  IntToSup (8, Eight);
Create (DixExp50, 4);  RoundLongRealToSup (1.0E50, DixExp50);
Create (SupT, 4);   Create (SupT1, 4);  Create (SupT2, 4);  Create (SupT3, 4); 
Create (P, 4);      Create (Tot, 4);    
Create (Eb, 2);     Create (Ec, 2);     Create (E, 2);    Create (h, 2);
Create (mm, 4);     Create (mmN, 4);
Create (P, 4);      Create (Pm1, 4);    Create (P2, 4);
Create (Rho, 4);    Create (LossRho, 4);
MCreateScal (mRed);    MCreateScal (m);    MCreateScal (MTemp);
MCreateScal (MTemp1);  MCreateScal (MTemp2);
MCreateScal (MTemp3);  MCreateScal (MTemp4);
MCreateScal (MThree);  MCreateScal (MFour);
MCreateScal (MFive);   MCreateScal (MSeven);   MCreateScal (MEight);
LIToMScal (3, MThree); LIToMScal (4, MFour);
LIToMScal (5, MFive);  LIToMScal (7, MSeven);  LIToMScal (8, MEight);
FOR  i := 0  TO  MMaxDim  DO  Create (VectSup [i], 2)  END;
MCreateScal (MTwoExp [0]);   MAffect (MOne, MTwoExp [0]);
FOR  i := 1  TO  MaxHighBit DO 
   MCreateScal (MTwoExp [i]); 
   MMultiply (MTwoExp [i-1], MTwo, MTwoExp [i]);
   END;
Tex := FALSE;
Streams := FALSE;
<* IF XDSV = "99" THEN *>
   CreateStream (RngBornes, "RngBornes");
   <* END *>
END LATIO.
