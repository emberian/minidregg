($base[0].providerMetering == null and
 $base[0].continuityProviderResourceId == null and
 $base[0].agentLifetimeDispatchFixed == null) and
(.providerMetering == null and
 .continuityProviderResourceId == null and
 .agentLifetimeDispatchFixed == null) and
(.providerServices == [
  {providerResourceId:7950,tariff:{version:"1",model:"bonsai2-27b-ptq1",
    inputMicroPerMillion:"0",outputMicroPerMillion:"0"}},
  {providerResourceId:7951,tariff:{version:"1",model:"bonsai2-27b-ptq1",
    inputMicroPerMillion:"0",outputMicroPerMillion:"0"}}]) and
(del(.providerServices,.providerMetering,.continuityProviderResourceId,
     .agentLifetimeDispatchFixed) ==
 ($base[0] | del(.providerServices,.providerMetering,
                 .continuityProviderResourceId,.agentLifetimeDispatchFixed)))
