{ agdaPackages }: with agdaPackages; rec {

  standard-library-meta = mkDerivation {
    pname = "standard-library-meta";
    version = "0.1";
    src = ./.;
    meta = { };
    libraryFile = "agda-stdlib-meta.agda-lib";
    buildInputs = [
      standard-library
      standard-library-classes
    ];
  };

  default = standard-library-meta;
}
