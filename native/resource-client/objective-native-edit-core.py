# Request edit for objective-native-acceptance.py: a client whose own pinned
# replay produced a different artifact than the stored one (one byte of the
# typed core). The local quote and endpoint 227 must refuse before signing.
art=bytearray.fromhex(request['source']['expectedArtifact']); art[-3]^=1
request['source']['expectedArtifact']=art.hex()
