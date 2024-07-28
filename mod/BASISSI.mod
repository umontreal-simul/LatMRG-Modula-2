IMPLEMENTATION MODULE BASISSI;

FROM MYINOUT  IMPORT WriteString, WriteInt, WriteLn, Write;
FROM NUM      IMPORT Sqrt;

FROM SUPINT   IMPORT SuperInteger, Create, Affect, WriteSup, ReadSup,
	             Delete;
FROM SUPCONV  IMPORT SupToLongReal, IntToSup, LongRealToSup;
FROM SUPARITH IMPORT ChangeSign, Add, Multiply, Subtract, AbsVal, Zero,
                     MultiplyIntSup, Equal, Smaller, Greater, AbsSizeOrd,
                     Divide, Positive, Negative, Quotient;
FROM SUPRAND  IMPORT SupRandom;
FROM CONFIG   IMPORT BMaxDim, BDim;
FROM SYSTEM   IMPORT ADDRESS;

VAR
   S1, S2, S3 : BScal;
   adr       : ADDRESS;



PROCEDURE BCreateScal (VAR S : BScal);
   BEGIN  Create (S, BSizeSI)  END BCreateScal;
   
PROCEDURE BDeleteScal (VAR S : BScal);
   BEGIN  Delete (S) END BDeleteScal;

PROCEDURE BCreateVect (VAR V : BVect; d1, d2 : BDim);
   VAR i : BDim;
   BEGIN
   FOR  i := d1  TO  d2  DO  Create(V[i], BSizeSI)  END
   END BCreateVect;
   
PROCEDURE BDeleteVect (VAR V : BVect; d1, d2 : BDim);
   VAR i : BDim;
   BEGIN
   FOR  i := d1  TO  d2  DO  Delete(V[i])  END
   END BDeleteVect;


PROCEDURE BCreateMatr (VAR M : BMatr; d1, d2 : BDim);
   VAR i : BDim;
   BEGIN
   IF  d1 <= d2  THEN
      IF  d1 > 0  THEN
         FOR i := 0 TO d1-1 DO BCreateVect(M[i], d1, d2) END
         END;
      FOR i := d1 TO d2 DO  BCreateVect(M[i], 0, d2) END
      END
   END BCreateMatr;
   

PROCEDURE BDeleteMatr (VAR M : BMatr; d1, d2 : BDim);
   VAR i : BDim;
   BEGIN
   IF  d1 <= d2  THEN
      IF  d1 > 0  THEN
         FOR i := 0  TO  d1-1 DO BDeleteVect(M[i], d1, d2) END
         END;
      FOR i := d1 TO d2 DO BDeleteVect(M[i], 0, d2) END
      END
   END BDeleteMatr;


PROCEDURE BReadScal (VAR S : BScal);
   BEGIN  ReadSup(S, 10) END BReadScal;


PROCEDURE BWriteScal (S : BScal; nb : CARDINAL);
   BEGIN  WriteSup (S, 10, nb) END BWriteScal;


PROCEDURE BWriteVect (VAR V : BVect;  n : BDim; nb : CARDINAL);
   VAR i : BDim;
   BEGIN
   FOR i := 1 TO n DO
      IF (i-1) MOD 4 = 0 THEN WriteLn END;
      BWriteScal (V [i], nb);
      IF (i<n) AND (i MOD 4 # 0) THEN Write ( CHR (9) ) END
      END
   END BWriteVect;


PROCEDURE BWriteMatr (VAR M : BMatr;  n : BDim; nb : CARDINAL);
   VAR i : BDim;
   BEGIN
   FOR i := 1 TO n DO
      WriteLn;  WriteString ('Line '); WriteInt ( i, 2 );
      BWriteVect ( M[i], n, nb )
      END
   END BWriteMatr;

PROCEDURE BProdScalVect (s : BScal; VAR V : BVect; d : BDim);
   VAR i : BDim;
   BEGIN
   FOR  i := 1  TO  d  DO
      Multiply(s, V[i], V[i])
      END
   END BProdScalVect;

PROCEDURE BProdScal (VAR U, V : BVect;  n : BDim; VAR S : BScal);
   VAR i : BDim;
   BEGIN
   IntToSup ( 0, S );
   FOR i := 1 TO n DO
      Multiply ( U [i], V [i], S1 );
      Add ( S, S1, S )
      END
   END BProdScal;

PROCEDURE BProdScalLR (VAR U, V : BVect;  n : BDim) : LONGREAL;
   VAR
      i : BDim;
      Sum, x, y : LONGREAL;
   BEGIN
   Sum := 0.0;
   FOR i := 1 TO n DO
      SupToLongReal (U [i], x);   SupToLongReal (V [i], y);
      Sum := Sum + (x * y)
      END;
   RETURN Sum
   END BProdScalLR;

PROCEDURE BProdScalSI (VAR U, V : BVect; n : BDim; Res : SuperInteger);
   BEGIN
   BProdScal (U, V, n, Res)
   END BProdScalSI;

PROCEDURE BL1NormLR (VAR V : BVect;  n : BDim) : LONGREAL;
   VAR 
      i      : BDim;
      Sum, y : LONGREAL;
   BEGIN
   Sum := 0.0;
   FOR i := 1 TO n DO  
      SupToLongReal (V[i], y);   Sum := Sum + ABS (y)  
      END;
   RETURN Sum
   END BL1NormLR;

PROCEDURE BL1NormSI (VAR V : BVect;  n : BDim;  S1 : SuperInteger);
   VAR 
      i : BDim;
   BEGIN
   IntToSup (0, S1);
   FOR i := 1 TO n DO
      IF Negative (V[i]) THEN Subtract (S1, V[i], S1)  
      ELSE Add (S1, V[i], S1) END;
      END
   END BL1NormSI;

PROCEDURE BL2NormLR (VAR V : BVect;  n : BDim) : LONGREAL;
   VAR
      i : BDim;
      Sum, x : LONGREAL;
   BEGIN
   Sum := 0.0;
   FOR i := 1 TO n DO
      SupToLongReal (V [i], x);
      Sum := Sum + (x * x)
      END;
   RETURN Sqrt (Sum)
   END BL2NormLR;

PROCEDURE BSupNormLR (VAR V : BVect;  n : BDim) : LONGREAL;
   VAR
      i      : BDim;
      Sup, y : LONGREAL;
   BEGIN
   Sup := 0.0;
   FOR i := 1 TO n DO  
      SupToLongReal (V[i], y); 
      IF (ABS (y) > Sup) THEN  Sup := ABS (y)  END;
      END;
   RETURN Sup
   END BSupNormLR;

PROCEDURE BSupNormSI (VAR V : BVect;  n : BDim;  S1 : SuperInteger);
   VAR
      i : BDim;
   BEGIN
   IntToSup (0, S1);
   FOR i := 1 TO n DO
      IF Negative (V[i]) THEN 
         ChangeSign (V[i], V[i]);
         IF Greater (V[i], S1) THEN Affect (V[i], S1) END;
         ChangeSign (V[i], V[i]);
      ELSE
         IF Greater (V[i], S1) THEN Affect (V[i], S1) END;
         END
      END;
   END BSupNormSI;

PROCEDURE BInc (VAR S : BScal; i : LONGINT);
   BEGIN
   IntToSup(i, S1);
   Add(S, S1, S)
   END BInc;

PROCEDURE BModifVectLR (VAR U, V : BVect;  c : LONGREAL;  n : BDim);
   VAR i : BDim;
   BEGIN
   LongRealToSup (c, S1);
   FOR i := 1 TO n DO
      Multiply (S1, V [i], S2);   Add (U [i], S2, U [i])
      END
   END BModifVectLR;


PROCEDURE BModifVectLI (VAR U, V : BVect;  c : LONGINT;  n : BDim);
   VAR i : BDim;
   BEGIN
   FOR i := 1 TO n DO
      MultiplyIntSup (c, V [i], S2);   Add (U [i], S2, U [i])
      END
   END BModifVectLI;

PROCEDURE BModifVect (VAR U, V : BVect;  c : BScal;  n : BDim);
   VAR i : BDim;
   BEGIN
   FOR i := 1 TO n DO
      Multiply (c, V [i], S2);   Add (U [i], S2, U [i])
      END
   END BModifVect;


PROCEDURE BChangeSign (VAR S : BScal);
   BEGIN
   ChangeSign (S, S)
   END BChangeSign;

PROCEDURE BSetNeg (VAR S : BScal);
   BEGIN IF Positive (S) THEN ChangeSign (S, S); END;
   END BSetNeg;

PROCEDURE BChangeSignVect (VAR V : BVect;  n : BDim);
   VAR i : BDim;
   BEGIN
   FOR i := 1 TO n DO  ChangeSign (V [i], V [i])  END
   END BChangeSignVect;


PROCEDURE BAffect (S : BScal; VAR T : BScal);
   BEGIN  Affect (S, T)  END BAffect;

PROCEDURE BExchange (VAR S, T : BScal);
   BEGIN
   adr := S; S := T; T := adr
   END BExchange;

PROCEDURE BEqual (S, T : BScal): BOOLEAN;
   BEGIN IF Equal (S, T) THEN RETURN TRUE ELSE RETURN FALSE END;
   END BEqual;


PROCEDURE BSmaller (S, T : BScal): BOOLEAN;
   BEGIN IF Smaller (S, T) THEN RETURN TRUE ELSE RETURN FALSE END;
   END BSmaller;


PROCEDURE BGreater (S, T : BScal): BOOLEAN;
   BEGIN IF Greater (S, T) THEN RETURN TRUE ELSE RETURN FALSE END;
   END BGreater;

PROCEDURE BAbsSizeOrd (S, T : BScal): INTEGER;
   BEGIN
   RETURN AbsSizeOrd (S, T)
   END BAbsSizeOrd;


PROCEDURE BAbs (S : BScal; VAR T : BScal);
   BEGIN AbsVal (S, T)  END BAbs;


PROCEDURE BAdd (S, T : BScal; VAR Res : BScal);
   BEGIN  Add (S, T, Res)  END BAdd;


PROCEDURE BMultiply (S, T : BScal; VAR Res : BScal);
   BEGIN  Multiply (S, T, Res)  END BMultiply;

PROCEDURE BDivideRound (S, T : BScal; VAR Q : BScal);        
   VAR
      cs : BOOLEAN;
   BEGIN
   IF  (Positive(S) AND Negative(T)) OR (Negative(S) AND Positive(T))  THEN
      cs := TRUE
   ELSE
      cs := FALSE
      END;    
   AbsVal (T, S1); AbsVal (S, S2);
   Divide (S2, S1, Q, S2);
   Add (S2, S2, S2);
   IF  Greater(S2, S1)  THEN  Add(Q, BOne, Q)  END;
   IF  cs  THEN  ChangeSign(Q, Q)   END
   END BDivideRound;

PROCEDURE BCopyVect (VAR U, V : BVect;  n : BDim);
   VAR i : BDim;
   BEGIN
   FOR i := 1 TO n DO  Affect (U [i], V [i])  END
   END BCopyVect;


PROCEDURE BCopyMatr (VAR M1, M2 : BMatr;  n : BDim);
   VAR i, j : BDim;
   BEGIN
   FOR i := 1 TO n DO
      FOR j := 1 TO n DO  Affect (M1 [i,j], M2 [i,j])  END  END
   END BCopyMatr;


PROCEDURE BConvLR (S : BScal): LONGREAL;
   VAR R : LONGREAL;
   BEGIN
   SupToLongReal (S , R);
   RETURN R;
   END BConvLR;

PROCEDURE BConvSI (R : BScal; S : SuperInteger);
   BEGIN
   Affect (R, S);
   END BConvSI;


PROCEDURE BAffectIdentMatr (VAR M : BMatr; n : BDim);
   VAR i, j : BDim;
   BEGIN
   FOR i := 1 TO n DO
      FOR j := 1 TO n DO
         IF i=j THEN IntToSup (1, M [i,j]) ELSE IntToSup (0, M [i,j]) END
         END
      END
   END BAffectIdentMatr;

(*
PROCEDURE BInvMatr (VAR W : BASISLR.BMatr ; X : BMatr ; n : BDim) ;
   VAR
   i,j   : BDim ;
   Y     : BASISLR.BMatr ;
   BEGIN
   BASISLR.BCreateMatr (Y) ;
   FOR i:= 1 TO n DO
      FOR j := 1 TO n DO
         Y[i][j] := BConvLR (X[i][j]) ;
         END ;
      END ;
   BASISLR.BInvMatr (W, Y, n);
   END BInvMatr ; 
*)

PROCEDURE BTrMatr (M : BMatr; VAR Mtr : BMatr; d : BDim);
   VAR
      i, j : BDim;
   BEGIN
   FOR  i := 1  TO  d  DO
      FOR  j := 1  TO  d  DO
         Affect (M[j,i], Mtr[i,j])
         END
      END
   END BTrMatr;

PROCEDURE BCanonicalVect (VAR V : BVect; i : BDim);
   VAR
      k : BDim;
   BEGIN
   FOR  k := 1  TO  BMaxDim  DO
      Affect(BZero, V[k])
      END;
   Affect(BOne, V[i])
   END BCanonicalVect;      


PROCEDURE BRandomScal (VAR s : BScal; m : BScal);
   BEGIN
   Subtract(m, BOne, S1);
   SupRandom(BZero, S1, s)
   END BRandomScal;

PROCEDURE LIToBScal (i : LONGINT; VAR S : BScal);
   BEGIN
   IntToSup(i, S)
   END LIToBScal;

PROCEDURE BEuclide (A, B : BScal;  VAR C, D, E, F, G : BScal);
   BEGIN
   BAffect (A, G);  BAffect (B, S3);
   IntToSup (1, C);  IntToSup (0, D);  IntToSup (0, E);  IntToSup (1, F);
   IF Zero (A) THEN
      BExchange (G, S3);  BExchange (C, E);  BExchange (D, F);  RETURN
      END; 
   WHILE  NOT Zero (S3)  DO
      BExchange (G, S3);  BExchange (C, E);  BExchange (D, F);
      Quotient (S3, G, S1);  ChangeSign (S1, S1);
      Multiply (S1, G, S2);  Add (S2, S3, S3);
      Multiply (S1, C, S2);  Add (S2, E, E);
      Multiply (S1, D, S2);  Add (S2, F, F);
      END
   END BEuclide;

(****************************************************************************)

BEGIN
BCreateScal(BZero); BCreateScal(BOne); BCreateScal(BMinusOne);
IntToSup(0, BZero); IntToSup(1, BOne);
ChangeSign (BOne, BMinusOne);
BCreateScal (S1); BCreateScal (S2); BCreateScal (S3);
END BASISSI.

