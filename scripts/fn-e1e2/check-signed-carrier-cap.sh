#!/bin/sh
# Read-only preflight for the qualified private fn POST recipe-v2 carrier.
set -eu
if [ "$#" -ne 2 ]; then
  echo "usage: $0 SIGNED-CARRIER MAX-ARTICLE-OCTETS" >&2
  exit 2
fi
case "$2" in
  262144|524288|1048576) ;;
  *) echo "unsupported private fn article cap: $2" >&2; exit 2 ;;
esac
perl - "$1" "$2" <<'PERL'
use strict;
use warnings;
my ($path, $cap) = @ARGV;
open my $fh, '<:raw', $path or die "cannot read carrier: $!\n";
local $/;
my $carrier = <$fh>;
defined($carrier) && length($carrier) or die "empty carrier\n";
$carrier =~ /\r\n\z/ or die "carrier lacks terminal CRLF\n";
$carrier !~ /\x00|(?<!\r)\n|\r(?!\n)/ or die "carrier has non-CRLF framing\n";
$carrier =~ /\r\n\r\n/ or die "carrier lacks header/body separator\n";
my $prefix = "Path: fn.example.invalid!not-for-mail\r\nInjection-Info: fn.example.invalid\r\n";
my $dots = () = $carrier =~ /(?:\A|\r\n)\./g;
my $served = length($carrier) + length($prefix);
my $wire = length($carrier) + $dots + 3; # dot-stuffing and final .CRLF
print "carrierBytes=", length($carrier), " fnAddedPrefixBytes=", length($prefix),
      " servedBytes=$served postWireBytes=$wire maxArticleOctets=$cap\n";
$served <= $cap or die "fn served article exceeds operator cap\n";
$wire <= $cap or die "conservative POST wire exceeds operator cap\n";
PERL
