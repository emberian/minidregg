# Request edit for objective-native-acceptance.py (row r14): an honest request whose envelope declares
# NO front-end work (replayBytes = coreBytes = 0), priced exactly by the tariff so only the work account
# can refuse it. The native route must refuse it by name (Reject.objectiveWork) before it replays.
c=request['capacity']; c['replayBytes']='0'; c['coreBytes']='0'
c['proofWork']=str(price(s['tariff'],c))
