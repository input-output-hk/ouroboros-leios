terraform {
  backend "gcs" {
  }

  required_providers {
    google = {
      source = "hashicorp/google"
    }
    googlesiteverification = {
      source  = "hectorj/googlesiteverification"
      version = "0.4.5"
    }
  }
}

provider "google" {
  credentials = file(var.google_service_credentials_json_file)
  project     = local.google_project_id
  region      = var.google_region
  zone        = var.google_zone
}
