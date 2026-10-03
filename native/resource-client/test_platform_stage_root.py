import importlib.util
from pathlib import Path
import io
import shlex
import tempfile
import json
import tarfile
import unittest
spec=importlib.util.spec_from_file_location("platform_stage_root",Path(__file__).with_name("platform-stage-root.py"))
stage=importlib.util.module_from_spec(spec);spec.loader.exec_module(stage)
class RootStageTests(unittest.TestCase):
    def archive(self,name,kind=tarfile.REGTYPE,link=""):
        stream=io.BytesIO()
        with tarfile.open(fileobj=stream,mode="w") as archive:
            item=tarfile.TarInfo(name);item.type=kind;item.linkname=link
            archive.addfile(item)
        stream.seek(0)
        return tarfile.open(fileobj=stream)
    def test_regular_source_member_allowed(self):
        with self.archive("deploy/mini.py") as archive:self.assertEqual(len(stage.safe_archive(archive)),1)
    def test_parent_path_refused(self):
        with self.archive("../../escape") as archive:
            with self.assertRaisesRegex(RuntimeError,"path escapes"):stage.safe_archive(archive)
    def test_absolute_path_refused(self):
        with self.archive("/etc/owned") as archive:
            with self.assertRaisesRegex(RuntimeError,"path escapes"):stage.safe_archive(archive)
    def test_symlink_refused_before_extraction(self):
        with self.archive("deploy/link",tarfile.SYMTYPE,"/etc/shadow") as archive:
            with self.assertRaisesRegex(RuntimeError,"link or special"):stage.safe_archive(archive)
    def test_hardlink_refused_before_extraction(self):
        with self.archive("deploy/link",tarfile.LNKTYPE,"../../outside") as archive:
            with self.assertRaisesRegex(RuntimeError,"link or special"):stage.safe_archive(archive)
    def test_mutable_git_state_refused(self):
        with self.archive(".git/config") as archive:
            with self.assertRaisesRegex(RuntimeError,"mutable build/Git"):stage.safe_archive(archive)
    def test_rewrite_is_boundary_exact_and_recursive(self):
        value={"role":"/old/host","physical":"/older/bwrap","nested":["/old",{"archive":"/old/source.tar"}]}
        self.assertEqual(stage.rewrite(value,"/old","/new"),
            {"role":"/new/host","physical":"/older/bwrap","nested":["/new",{"archive":"/new/source.tar"}]})

    def test_existing_relative_regular_fixture_link_allowed(self):
        stream=io.BytesIO()
        with tarfile.open(fileobj=stream,mode="w") as archive:
            target=tarfile.TarInfo("fixture/a");archive.addfile(target)
            link=tarfile.TarInfo("fixture/b");link.type=tarfile.SYMTYPE;link.linkname="a";archive.addfile(link)
        stream.seek(0)
        with tarfile.open(fileobj=stream) as archive:self.assertEqual(len(stage.safe_archive(archive)),2)

    def test_credential_allocator_binds_exact_frame_operator_and_only_two_arguments(self):
        text=stage.credential_wrapper(Path("/var/lib/mini-r2"),"hbox")
        command=shlex.split(text.split("exec ",1)[1].strip())
        self.assertEqual(command,["/usr/bin/python3","-I","/var/lib/mini-r2/usr/local/lib/mini/credential-namespace.py","/var/lib/mini-r2","hbox","$@"])
        self.assertIn("[[ $# == 2 ]]",text)
        self.assertNotIn("MINI_ROOT",text)
        with self.assertRaisesRegex(RuntimeError,"operator account invalid"):
            stage.credential_wrapper(Path("/var/lib/mini-r2"),"hbox;touch")

    def test_metadata_hash_follows_selected_component_not_candidate(self):
        with tempfile.TemporaryDirectory() as folder:
            staged=Path(folder);component=staged/"launcher/component-manifest.json";component.parent.mkdir()
            component.write_text(json.dumps({"host":"/family/host"}));original=stage.sha(component)
            (staged/"candidate.json").write_text("different provenance bytes")
            value={"componentManifest":"/family/launcher/component-manifest.json","componentManifestSha256":original}
            rewritten={};result=stage.metadata_variant(value,Path("/family"),Path("/frame/candidate"),staged,rewritten)
            self.assertEqual(result["componentManifest"],"/frame/candidate/launcher/component-manifest.json")
            self.assertEqual(result["componentManifestSha256"],stage.sha(component))
            self.assertNotEqual(result["componentManifestSha256"],stage.sha(staged/"candidate.json"))
            self.assertEqual(stage.read(component),{"host":"/frame/candidate/host"})
            self.assertEqual(stage.metadata_variant(value,Path("/family"),Path("/frame/candidate"),staged,rewritten),result)
    def test_metadata_dependency_mutation_refused_before_rewrite(self):
        with tempfile.TemporaryDirectory() as folder:
            staged=Path(folder);component=staged/"component.json";component.write_text("{}")
            value={"componentManifest":"/family/component.json","componentManifestSha256":"0"*64}
            with self.assertRaisesRegex(RuntimeError,"original bytes differ"):
                stage.metadata_variant(value,Path("/family"),Path("/frame/candidate"),staged,{})
            self.assertEqual(component.read_text(),"{}")

    def test_internal_fixture_directory_link_allowed_without_alias_writes(self):
        stream=io.BytesIO()
        with tarfile.open(fileobj=stream,mode="w") as archive:
            target=tarfile.TarInfo("fixture/a");target.type=tarfile.DIRTYPE;archive.addfile(target)
            archive.addfile(tarfile.TarInfo("fixture/a/head.json"))
            link=tarfile.TarInfo("fixture/b");link.type=tarfile.SYMTYPE;link.linkname="a";archive.addfile(link)
        stream.seek(0)
        with tarfile.open(fileobj=stream) as archive:self.assertEqual(len(stage.safe_archive(archive)),3)
    def test_member_traversing_directory_link_refused(self):
        stream=io.BytesIO()
        with tarfile.open(fileobj=stream,mode="w") as archive:
            target=tarfile.TarInfo("fixture/a");target.type=tarfile.DIRTYPE;archive.addfile(target)
            link=tarfile.TarInfo("fixture/b");link.type=tarfile.SYMTYPE;link.linkname="a";archive.addfile(link)
            archive.addfile(tarfile.TarInfo("fixture/b/overwrite.json"))
        stream.seek(0)
        with tarfile.open(fileobj=stream) as archive:
            with self.assertRaisesRegex(RuntimeError,"member traverses a link"):stage.safe_archive(archive)
