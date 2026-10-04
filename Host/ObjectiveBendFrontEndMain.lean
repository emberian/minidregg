/- `lean --run Host/ObjectiveBendFrontEndMain.lean COMMAND ...`: the Objective Bend front end
(`Host.ObjectiveBendFrontEnd`) against built oleans. The native Host runs the same code as
`minidregg-host /dev/null objective-front COMMAND ...`. -/
import Host.ObjectiveBendFrontEnd

def main (arguments : List String) : IO UInt32 := Minidregg.Host.ObjectiveBendFrontEnd.run arguments
