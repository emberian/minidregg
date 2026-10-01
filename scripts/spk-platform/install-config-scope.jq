($base[0].providerMetering == null and
 $base[0].continuityProviderResourceId == null and
 $base[0].agentLifetimeDispatchFixed == null) and
(.providerMetering == null and
 .continuityProviderResourceId == null and
 .agentLifetimeDispatchFixed == null) and
(.storageBinary == $storeHelper and .signatureBinary == $signatureHelper) and
(.providerServices == ([7950, 7951] | map(
  {providerResourceId:.,tariff:{version:"1",model:"bonsai2-27b-ptq1",routes:{
    user:{perOp:"0"},
    pool:{perOp:"0",inputMicroPerMillion:"0",outputMicroPerMillion:"0"},
    homelab:{perOp:"0",inputMicroPerMillion:"0",outputMicroPerMillion:"0"}}}}))) and
(del(.storageBinary,.signatureBinary,.providerServices,.providerMetering,
     .continuityProviderResourceId,.agentLifetimeDispatchFixed) ==
 ($base[0] | del(.providerServices,.providerMetering,
                 .storageBinary,.signatureBinary,.continuityProviderResourceId,
                 .agentLifetimeDispatchFixed)))
