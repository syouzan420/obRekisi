{ system ? builtins.currentSystem
, obelisk ? import ./.obelisk/impl {
    inherit system;
    iosSdkVersion = "16.1";

    # You must accept the Android Software Development Kit License Agreement at
    # https://developer.android.com/studio/terms in order to build Android apps.
    # Uncomment and set this to `true` to indicate your acceptance:
    config.android_sdk.accept_license = true;

    # In order to use Let's Encrypt for HTTPS deployments you must accept
    # their terms of service at https://letsencrypt.org/repository/.
    # Uncomment and set this to `true` to indicate your acceptance:
    # terms.security.acme.acceptTerms = false;
  }
}:
with obelisk;
project ./. ({ ... }: {

  android = {
    applicationId = "org.yokop.rekisi";
    displayName = "Rekisi";
    resources = reflex-platform.android.buildIcons {
      src = ./assets/chara.png;
    };
    version = {
      code = "1";
      name = "0.1";
    };
  };
  ios.bundleIdentifier = "rog.yokop.rekisi";
  ios.bundleName = "Rekisi";
})
