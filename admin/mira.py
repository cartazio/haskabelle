"""
    Test configuration descriptions for mira.
"""

import os
from os import path

from configurations import Isabelle as isabelle


@configuration(repos = [Haskabelle, Isabelle], deps = [(isabelle.HOL, [1])])
def Haskabelle(env, case, paths, dep_paths, playground):

    """Testing integration of Haskabelle with Isabelle"""

    (loc_haskabelle, loc_isabelle) = paths
    (dep_isabelle,) = dep_paths
    isabelle.prepare_isabelle_repository(loc_isabelle, env.settings.contrib, dep_isabelle)
    os.chdir(loc_haskabelle)

    (return_code, log) = env.run_process('admin/makedist', '--regression',
        ISABELLE_HOME = loc_isabelle,
        ISABELLE_DOC_SRC = path.join(loc_isabelle, 'doc-src'),
        ISABELLE_PROCESS = path.join(loc_isabelle, 'bin', 'isabelle-process'),
        ISABELLE_TOOL = path.join(loc_isabelle, 'bin', 'isabelle'),
        DIST_HOME = playground)

    return (return_code == 0, isabelle.extract_isabelle_run_summary(log), {}, {'log': log}, None)
