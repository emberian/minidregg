(.storageBinary == $storeHelper and .signatureBinary == $signatureHelper) and
(del(.storageBinary,.signatureBinary) ==
 ($base[0] | del(.storageBinary,.signatureBinary)))
