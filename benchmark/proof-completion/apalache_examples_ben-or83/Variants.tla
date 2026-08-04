------------------------------- MODULE Variants -------------------------------

UNIT == "U_OF_UNIT"

Variant(__tagName, __value) ==

    [ t \in { __tagName } |-> __value ]

VariantFilter(__tagName, __S) ==
    
    { __f[__tagName]: __f \in { __e \in __S: __tagName \in DOMAIN __e } }

VariantTag(__variant) ==
    
    CHOOSE __tag \in DOMAIN __variant: TRUE

VariantGetOrElse(__tagName, __variant, __defaultValue) ==
    
    IF __tagName \in DOMAIN __variant
    THEN __variant[__tagName]
    ELSE __defaultValue

VariantGetUnsafe(__tagName, __variant) ==
    
    __variant[__tagName]

===============================================================================
