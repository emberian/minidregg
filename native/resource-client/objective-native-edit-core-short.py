# Request edit for objective-native-acceptance.py (row r15): the source bytes are declared but the typed
# core one byte short of the selected artifact's, priced exactly by the tariff. Refused by name
# (Reject.objectiveWork naming the core stage) before the replay generates the core.
c=request['capacity']; c['coreBytes']=str(int(s['publication']['frontEnd']['coreBytes'])-1)
c['proofWork']=str(price(s['tariff'],c))
