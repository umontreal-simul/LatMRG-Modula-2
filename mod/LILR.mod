IMPLEMENTATION MODULE LILR;

FROM NUM     IMPORT LIToLR, Trunc, t;
FROM SUPINT  IMPORT SuperInteger, NumBits;
FROM SUPCONV IMPORT SupToInt, IntToSup, SupToLongReal, LongRealToSup;
FROM MULTLI  IMPORT MScal;             (* LONGINT.                        *)
FROM BASISLR IMPORT BScal;             (* LONGREAL.                       *)
FROM MYINOUT IMPORT WriteLn, WriteString;

PROCEDURE MScalToBScal (S : MScal;  VAR R : BScal);
   BEGIN  R := LIToLR (S)  END MScalToBScal;

PROCEDURE BScalToMScal (S : BScal;  VAR R : MScal);
   BEGIN  R := Trunc (S)  END BScalToMScal;

PROCEDURE SupToBScal (S : SuperInteger; VAR R : BScal);
   BEGIN  
   IF  NumBits (S) <= t  THEN
      SupToLongReal (S, R) 
   ELSE
      WriteLn;
      WriteString ('ERROR SupToBScal, overflow');
      WriteLn; HALT 
      END
   END SupToBScal;

PROCEDURE SupToMScal (S : SuperInteger; VAR R : MScal);
   BEGIN  SupToInt (S, R)  END SupToMScal;

PROCEDURE BScalToSup (S : BScal; R : SuperInteger);
   BEGIN  LongRealToSup (S, R)  END BScalToSup;

PROCEDURE MScalToSup (S : MScal;  R : SuperInteger);
   BEGIN  IntToSup (S, R)  END MScalToSup;

END LILR.
