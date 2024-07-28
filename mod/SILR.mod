IMPLEMENTATION MODULE SILR;

FROM NUM      IMPORT t;
FROM SUPINT   IMPORT SuperInteger, Affect, NumBits;
FROM SUPCONV  IMPORT SupToLongReal, LongRealToSup, RoundLongRealToSup;
FROM MULTSI   IMPORT MScal;            (* SuperInteger.                   *)
FROM BASISLR  IMPORT BScal;            (* LONGREAL.                       *)
FROM MYINOUT  IMPORT WriteLn, WriteString;


PROCEDURE MScalToBScal (S : MScal;  VAR R : BScal);
   BEGIN  SupToLongReal (S, R)   END MScalToBScal;

PROCEDURE BScalToMScal (S : BScal;  VAR R : MScal);
   BEGIN  RoundLongRealToSup (S, R)  END BScalToMScal;

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
   BEGIN  Affect (S, R)  END SupToMScal;

PROCEDURE BScalToSup (S : BScal; R : SuperInteger);
   BEGIN  LongRealToSup (S, R)  END BScalToSup;

PROCEDURE MScalToSup (S : MScal; R : SuperInteger);
   BEGIN  Affect (S, R)  END MScalToSup;

END SILR.
