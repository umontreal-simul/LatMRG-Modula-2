IMPLEMENTATION MODULE LISI;

FROM SUPCONV  IMPORT SupToInt, IntToSup;
FROM MULTLI   IMPORT MScal;             (* LONGINT.                        *)
FROM BASISSI  IMPORT BScal;             (* SuperInteger.                   *)
FROM SUPINT   IMPORT SuperInteger, Affect;

PROCEDURE MScalToBScal (S : MScal;  VAR R : BScal);
   BEGIN  IntToSup (S, R)  END MScalToBScal;

PROCEDURE BScalToMScal (S : BScal;  VAR R : MScal);
   BEGIN  SupToInt (S, R)  END BScalToMScal;

PROCEDURE SupToBScal (S : SuperInteger; VAR R : BScal);
   BEGIN  Affect (S, R)  END SupToBScal;

PROCEDURE SupToMScal (S : SuperInteger; VAR R : MScal);
   BEGIN  SupToInt (S, R)  END SupToMScal;

PROCEDURE BScalToSup (S : BScal; R : SuperInteger);
   BEGIN  Affect (S, R)  END BScalToSup;

PROCEDURE MScalToSup (S : MScal;  R : SuperInteger);
   BEGIN  IntToSup (S, R)  END MScalToSup;

END LISI.
