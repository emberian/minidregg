($base[0].providerMetering == null and
 $base[0].continuityProviderResourceId == null and
 $base[0].agentLifetimeDispatchFixed == null) and
(.providerMetering == null and
 .continuityProviderResourceId == null and
 .agentLifetimeDispatchFixed == null) and
(.storageBinary == $storeHelper and .signatureBinary == $signatureHelper) and
(.providerServices == [
  {providerResourceId:7950,tariff:{version:"1",model:"bonsai2-27b-ptq1",
    inputMicroPerMillion:"0",outputMicroPerMillion:"0"}},
  {providerResourceId:7951,tariff:{version:"1",model:"bonsai2-27b-ptq1",
    inputMicroPerMillion:"0",outputMicroPerMillion:"0"}}]) and
(del(.storageBinary,.signatureBinary,.providerServices,.providerMetering,
     .continuityProviderResourceId,.agentLifetimeDispatchFixed) ==
 ($base[0] | del(.providerServices,.providerMetering,
                 .storageBinary,.signatureBinary,.continuityProviderResourceId,
                 .agentLifetimeDispatchFixed)))
