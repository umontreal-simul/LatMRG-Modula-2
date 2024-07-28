IMPLEMENTATION MODULE BASISLR;

FROM MYINOUT  IMPORT WriteString, WriteInt, WriteLn;
FROM NUM      IMPORT LIToLR, WriteLR, TruncLR, ReadLR, RoundLR, Sqrt;
FROM SUPINT   IMPORT SuperInteger, Create;
FROM SUPCONV  IMPORT IntToSup, LongRealToSup, RoundLongRealToSup;
FROM SUPARITH IMPORT Add, Multiply;
FROM CONFIG   IMPORT BMaxDim, BDim;

<* IF XDSV = "99" THEN *>
   FROM RAND     IMPORT RandU01, RngStream, CreateStream;
<* ELSE *>
   FROM RAND     IMPORT Uniform01;
   <* END *>

VAR
   T1, T2, zero : SuperInteger;
<* IF XDSV = "99" THEN *>
   RngBASISLR : RngStream;
   <* END *>



PROCEDURE BCreateScal (VAR S : BScal);
   BEGIN  END BCreateScal;
   
PROCEDURE BDeleteScal (VAR S : BScal);
   BEGIN  END BDeleteScal;


PROCEDURE BCreateVect (VAR V : BVect; d1, d2 : BDim);
   BEGIN
   END BCreateVect;
   
PROCEDURE BDeleteVect (VAR V : BVect; d1, d2 : BDim);
   BEGIN
   END BDeleteVect;


PROCEDURE BCreateMatr (VAR M : BMatr; d1, d2 : BDim);
   BEGIN
   END BCreateMatr;
   
PROCEDURE BDeleteMatr (VAR M : BMatr; d1, d2 : BDim);
   BEGIN
   END BDeleteMatr;


PROCEDURE BReadScal (VAR S : BScal);
   BEGIN  ReadLR(S); END BReadScal;

PROCEDURE BWriteScal (S : BScal; nb : CARDINAL);
   BEGIN  WriteLR (S, nb, 1, 2)  END BWriteScal;


PROCEDURE BWriteVect (VAR V : BVect;  n : BDim; nb : CARDINAL);
   VAR i : BDim;
   BEGIN
   FOR i := 1 TO n DO
      IF (i-1) MOD 4 = 0 THEN WriteLn END;
      BWriteScal (V [i], nb);  WriteString(' ')
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

(***************************************************************************)

PROCEDURE BProdScalVect (s : BScal; VAR V : BVect; d : BDim);
   VAR 
      i : BDim;
   BEGIN
   FOR  i := 1  TO  d  DO   V[i] := s * V[i]  END
   END BProdScalVect;

PROCEDURE BProdScal (VAR U, V : BVect;  n : BDim; VAR S : BScal);
   VAR 
      i : BDim;
   BEGIN
   S := 0.0;
   FOR i := 1 TO n DO  S := S + U [i] * V [i]  END;
   END BProdScal;


PROCEDURE BProdScalLR (VAR U, V : BVect;  n : BDim) : LONGREAL;
   VAR
      i   : BDim;
      Sum : LONGREAL;
   BEGIN
   Sum := 0.0;
   FOR i := 1 TO n DO  Sum := Sum + U [i] * V [i]  END;
   RETURN Sum
   END BProdScalLR;

PROCEDURE BProdScalSI (VAR U, V : BVect;  n : BDim; Res : SuperInteger);
   VAR
      i : BDim;
   BEGIN
   LongRealToSup(0.0, Res);
   FOR  i := 1  TO  n  DO
      LongRealToSup(U[i], T1);
      LongRealToSup(V[i], T2);  
      Multiply(T1, T2, T1);
      Add(Res, T1, Res)
      END
   END BProdScalSI;

PROCEDURE BL1NormLR (VAR V : BVect;  n : BDim) : LONGREAL;
   VAR 
      i   : BDim;
      Sum : LONGREAL;
   BEGIN
   Sum := 0.0;
   FOR i := 1 TO n DO  Sum := Sum + ABS (V [i])  END;
   RETURN Sum
   END BL1NormLR;

PROCEDURE BL1NormSI (VAR V : BVect;  n : BDim;  S1 : SuperInteger);
   VAR 
      x : LONGREAL;
   BEGIN
   x := BL1NormLR (V, n);   RoundLongRealToSup (x, S1);
   END BL1NormSI;

PROCEDURE BL2NormLR (VAR V : BVect;  n : BDim) : LONGREAL;
   VAR
      i   : BDim;
      Sum : LONGREAL;
   BEGIN
   Sum := 0.0;
   FOR i := 1 TO n DO  Sum := Sum + V [i] * V [i]  END;
   RETURN Sqrt (Sum)
   END BL2NormLR;

PROCEDURE BSupNormLR (VAR V : BVect;  n : BDim) : LONGREAL;
   VAR
      i   : BDim;
      Sup : LONGREAL;
   BEGIN
   Sup := 0.0;
   FOR i := 1 TO n DO  
      IF (ABS (V[i]) > Sup) THEN  Sup := ABS (V[i])  END;
      END;
   RETURN Sup
   END BSupNormLR;

PROCEDURE BSupNormSI (VAR V : BVect;  n : BDim;  S1 : SuperInteger);
   VAR
      x : LONGREAL;
   BEGIN
   x := BSupNormLR (V, n);   RoundLongRealToSup (x, S1);
   END BSupNormSI;

PROCEDURE BModifVectLR (VAR U, V : BVect;  c : LONGREAL;  n : BDim);
   VAR i : BDim;
   BEGIN
   FOR i := 1 TO n DO  U [i] := U [i] + c * V [i]  END
   END BModifVectLR;


PROCEDURE BModifVectLI (VAR U, V : BVect;  c : LONGINT;  n : BDim);
   VAR 
      i : BDim;
      cLR : LONGREAL;
   BEGIN
   cLR := LIToLR(c);
   FOR i := 1 TO n DO  U[i] := U[i] + cLR*V[i]  END
   END BModifVectLI;


PROCEDURE BModifVect (VAR U, V : BVect;  c : BScal;  n : BDim);
   VAR i : BDim;
   BEGIN
   FOR i := 1 TO n DO  U [i] := U [i] + c * V [i]  END
   END BModifVect;


PROCEDURE BChangeSign (VAR S : BScal);
   BEGIN
   S := -S
   END BChangeSign;

PROCEDURE BSetNeg (VAR S : BScal);
   BEGIN IF  S > 0.0  THEN  S := -1.0  END
   END BSetNeg;

PROCEDURE BChangeSignVect (VAR V : BVect;  n : BDim);
   VAR i : BDim;
   BEGIN
   FOR i := 1 TO n DO  V [i] := -V [i]  END
   END BChangeSignVect;

PROCEDURE BAffect (S : BScal; VAR T : BScal);
   BEGIN  T := S  END BAffect;

PROCEDURE BExchange (VAR S, T : BScal);
   VAR
      U : BScal;
   BEGIN
   U := S;  S := T;  T := U
   END BExchange;

PROCEDURE BEqual (S, T : BScal): BOOLEAN;
   BEGIN IF S = T THEN RETURN TRUE ELSE RETURN FALSE END;
   END BEqual;


PROCEDURE BSmaller (S, T : BScal): BOOLEAN;
   BEGIN IF S < T THEN RETURN TRUE ELSE RETURN FALSE END;
   END BSmaller;


PROCEDURE BGreater (S, T : BScal): BOOLEAN;
   BEGIN IF S > T THEN RETURN TRUE ELSE RETURN FALSE END;
   END BGreater;

PROCEDURE BAbsSizeOrd (S, T : BScal): INTEGER;
   BEGIN
   IF ABS(S) = ABS(T)  THEN  RETURN  0
   ELSIF  ABS(S) < ABS(T)  THEN  RETURN  1
   ELSE  RETURN  -1  END
   END BAbsSizeOrd;
      
PROCEDURE BAbs (S : BScal; VAR T : BScal);
   BEGIN T := ABS (S)  END BAbs;


PROCEDURE BAdd (S, T : BScal; VAR Res : BScal);
   BEGIN Res := S + T  END BAdd;

PROCEDURE BInc (VAR S : BScal; i : LONGINT);
   BEGIN S := S + LFLOAT(i);  END BInc;

PROCEDURE BMultiply (S, T : BScal; VAR Res : BScal);
   BEGIN Res := S * T  END BMultiply;


PROCEDURE BDivideRound (S, T : BScal; VAR Res : BScal);
   BEGIN Res := RoundLR (S / T)  END BDivideRound;


PROCEDURE BCopyVect (VAR U, V : BVect;  n : BDim);
   VAR i : BDim;
   BEGIN
   FOR i := 1 TO n DO  V [i] := U [i]  END
   END BCopyVect;


PROCEDURE BCopyMatr (VAR M1, M2 : BMatr;  n : BDim);
   VAR i, j : BDim;
   BEGIN
   FOR i := 1 TO n DO
      FOR j := 1 TO n DO  M2 [i,j] := M1 [i,j]  END  END
   END BCopyMatr;


PROCEDURE BConvLR (S : BScal): LONGREAL;
   BEGIN
   RETURN S;
   END BConvLR;

PROCEDURE BConvSI (R : BScal; S : SuperInteger);
   BEGIN
   LongRealToSup (R, S);
   END BConvSI;

PROCEDURE BAffectIdentMatr (VAR M : BMatr; n : BDim);
   VAR
      i, j : BDim;
   BEGIN
   FOR i := 1 TO n DO
      FOR j := 1 TO n DO
         IF i=j THEN M [i,j] := 1.0; ELSE M [i,j] := 0.0  END;
         END
      END
   END BAffectIdentMatr;


(*							(* Modif. de RC *)
PROCEDURE BInvMatr (VAR X : BMatr; V : BMatr; n : BDim) ;
   (* Inversion matricielle par la methode de Gauss avec pivotage *)
   (* partiel normalise                                           *)

   VAR
   i, j, k, d : BDim ;
   P          : ARRAY BDim OF BDim ;
   m, tempo   : BScal ;
   B, W       : BMatr ;
   OK         : BOOLEAN ;
   D          : ARRAY BDim OF BScal ;

   PROCEDURE BAbs (x : BScal) : BScal ;
      BEGIN
      IF x<0.0 THEN RETURN -x
      ELSE RETURN x; 
      END ;
      END BAbs ;


   PROCEDURE Chercher (VAR i : BDim; k : BDim) ;
   VAR j : BDim ;
      BEGIN
      i:=k ;
      FOR j := i+1 TO n DO 
         IF BAbs(W[j][k])/D[j] >= BAbs(W[i][k])/D[i] THEN i:=j ; END ;
         END ;
      END Chercher ;

   PROCEDURE Interchange (VAR i, k : BDim) ;
      VAR temp : CARDINAL ;
      BEGIN
      temp := k ;
      k := i ;
      i := temp ;
      END Interchange;

   PROCEDURE BAbsMax (VAR k : BScal; i : BDim) ;
      VAR j : BDim ;
      BEGIN
      k:=BAbs(V[i][1]) ;
      FOR j := 1 TO n DO
         IF BAbs(V[i][j])>k THEN k:=BAbs(V[i][j]) ; END ;
         END ;
      END BAbsMax ;

   BEGIN     (* BInvMatr *)
   d := 1 ;
   OK := TRUE ;
   BCreateMatr (B) ;
   BCreateMatr (W) ;
   BAffectIdentMatr (B, n) ;
   FOR i := 1 TO n DO 
      P[i] := i ;
      END ;

   FOR i := 1 TO n DO
      BAbsMax (D[i], i) ;
      END ;

   BCopyMatr (V, W, n) ;
   FOR k := 1 TO n-1 DO
      Chercher (i,k) ;
      IF OK=TRUE THEN Interchange (P[i], P[k]) ;
      FOR i := k+1 TO n DO
         m := W[P[i]][k] / W[P[k]][k] ;
         W[P[i]][k] := m ;
         FOR j := k+1 TO n DO
            W[P[i]][j] := W[P[i]][j] - m*W[P[k]][j] ;
            END ;
         B[P[i]][d] := B[P[i]][d] - m*B[P[k]][d] ;
         END ;
      END ;
   END;
   FOR k := n TO 1 BY -1 DO
      tempo := 0.0 ;
      FOR j := k+1 TO n DO
         tempo := W[P[k]][j]*X[j][d] + tempo ;
         END;
      X[k][d] := (B[P[k]][d] - tempo) / W[P[k]][k] ;
      END ;
   FOR d := 2 TO n DO
      FOR i := 2 TO n DO
         tempo := 0.0 ;
         FOR j := 1 TO i-1 DO
            tempo := tempo + W[P[i]][j]*B[P[j]][d] ;
            END ;
         B[P[i]][d] := B[P[i]][d] - tempo ;
         END ;
      FOR k := n TO 1 BY -1 DO
         tempo := 0.0 ;
         FOR j := k+1 TO n DO
            tempo := tempo + W[P[k]][j]*X[j][d] ;
            END ;
         X[k][d] := (B[P[k]][d] - tempo) / W[P[k]][k] ;
         END ;
      END ;
   END BInvMatr ;
*)
         
PROCEDURE BTrMatr (M : BMatr; VAR Mtr : BMatr; d : BDim);
   VAR
      i, j : BDim;
   BEGIN
   FOR  i := 1  TO  d  DO
      FOR  j := 1  TO  d  DO
         Mtr[i,j] := M[j,i]
         END
      END
   END BTrMatr;

(***************************************************************************)

PROCEDURE BCanonicalVect (VAR V : BVect; i : BDim);
   VAR
      k : BDim;
   BEGIN
   FOR  k := 1  TO  BMaxDim  DO
      V[k] := 0.0
      END;
   V[i] := 1.0
   END BCanonicalVect;      

(***************************************************************************)

PROCEDURE BRandomScal (VAR s : BScal; m : BScal);
   VAR
   BEGIN
<* IF XDSV = "99" THEN *>
   s := TruncLR (RandU01 (RngBASISLR) * m)
<* ELSE *>
   s := TruncLR (Uniform01 (1) * m)
   <* END *>


   END BRandomScal;

(***************************************************************************)

PROCEDURE LIToBScal (i : LONGINT; VAR S : BScal);
   BEGIN
   S := LIToLR (i);
   END LIToBScal;

(***************************************************************************)

PROCEDURE GCD2vect (VAR V : VectLI;  k, n : BDim) : LONGINT;
   (* Calcule le plus grand commun diviseur de V[k],...,V[n]. *)
   VAR
      i : BDim;
      c, d, r : LONGINT;
   BEGIN
   d := ABS (V[k]);
   i := k+1;
   WHILE (d#1) AND (i<=n) DO
      c := ABS (V[i]);
      WHILE c#0 DO  r := d MOD c;  d := c;  c := r  END;  
      (* d = GCD (d, V[i]). *)
      INC (i);
      END;
   RETURN d;
   END GCD2vect;

(***************************************************************************)

PROCEDURE BEuclide (A, B : BScal;  VAR C, D, E, F, G : BScal);
   VAR
      XX, YY, ZZ, temp : LONGREAL;
   BEGIN
   G := A;  ZZ := B;
   C := 1.0;  D := 0.0;  E := 0.0;  F := 1.0;
   IF (A = 0.0) THEN
      temp := ZZ;   ZZ := G;   G := temp;
      temp := C;   C := E;   E := temp;
      temp := D;   D := F;   F := temp;
      RETURN
      END; 
   WHILE  (ZZ <> 0.0)  DO
      temp := ZZ;   ZZ := G;   G := temp;
      temp := C;   C := E;   E := temp;
      temp := D;   D := F;   F := temp;
      XX := -TruncLR (ZZ / G);
      YY := XX * G;   ZZ := YY + ZZ;
      YY := XX * C;   E := YY + E;
      YY := XX * D;   F := YY + F;
      END
   END BEuclide;

(*************************************************************************)

BEGIN
BZero := 0.0;    BOne := 1.0;
Create (zero, 2);   Create (T1, 2);   Create (T2, 2);
IntToSup (0, zero);
BMinusOne := -1.0;
<* IF XDSV = "99" THEN *>
   CreateStream (RngBASISLR, "RngBASISLR");
   <* END *>
END BASISLR.
